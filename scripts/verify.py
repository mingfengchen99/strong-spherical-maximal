#!/usr/bin/env python3
"""Build and audit this Lean project using Python 3.9+ and the standard library."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
SOURCES = ROOT / "src"
LOGS = ROOT / ".verification"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def lean_code(source):
    """Blank nested comments and string literals, preserving line positions."""
    out = list(source)
    depth = 0
    quoted = False
    i = 0
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                out[i:i + 2] = "  "
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                out[i:i + 2] = "  "
                i += 2
            else:
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif quoted:
            if source[i] == "\\" and i + 1 < len(source):
                out[i] = " "
                if source[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
            else:
                quoted = source[i] != '"'
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            out[i:i + 2] = "  "
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            out[i:end] = " " * (end - i)
            i = end
        elif source[i] == '"':
            quoted = True
            out[i] = " "
            i += 1
        else:
            i += 1
    require(depth == 0 and not quoted, "Unterminated Lean comment or string")
    return "".join(out)


def sources_and_declarations(check_snapshot):
    config = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    match = re.search(r"^defaultTargets = (\[.*\])$", config, re.M)
    require(match is not None, "Expected a one-line defaultTargets list")
    modules = json.loads(match.group(1))
    libraries = re.findall(r'\[\[lean_lib\]\]\s*name = "([\w]+)"', config)
    require(len(modules) == len(set(modules)), "Duplicate default target")
    require(set(modules) == set(libraries), "Default targets and libraries differ")
    require(re.search(r'^srcDir = "src"$', config, re.M) is not None,
            "Expected the package source directory to be src/")
    require(not any(ROOT.glob("*.lean")), "Proof modules belong in src/")
    require(set(SOURCES.rglob("*.lean")) == {SOURCES / (m + ".lean") for m in modules},
            "Every proof module in src/ must be a registered default target")
    baseline = {}
    if check_snapshot:
        snapshot = ROOT / "docs/verification/sources.sha256"
        for line in snapshot.read_text(encoding="utf-8").splitlines():
            digest, name = line.split()
            baseline[name] = digest
        require(set(baseline) == {m + ".lean" for m in modules},
                "Approved snapshot and current source list differ")

    declarations = []
    for module in modules:
        path = SOURCES / (module + ".lean")
        data = path.read_bytes()
        if check_snapshot:
            require(hashlib.sha256(data).hexdigest() == baseline[path.name],
                    "Approved source changed: " + path.name)
        code = lean_code(data.decode("utf-8"))
        forbidden = re.search(r"\b(sorry|admit|unsafe|axiom|opaque|native_decide)\b", code)
        require(forbidden is None, "Forbidden proof token in " + path.name +
                (": " + forbidden.group(0) if forbidden else ""))
        namespaces = set(re.findall(r"^namespace\s+(\S+)", code, re.M))
        require(len(namespaces) == 1, "Expected one namespace per module: " + module)
        namespace = next(iter(namespaces))
        names = re.findall(
            r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?"
            r"(?:def|abbrev|theorem|lemma|instance|structure)\s+([\w'.]+)",
            code, re.M)
        require(bool(names), "No named declarations found in " + module)
        declarations.extend(namespace + "." + name for name in names)
    require(len(declarations) == len(set(declarations)), "Duplicate declaration name")
    print("Source guard passed: {} modules, {} named public declarations".format(
        len(modules), len(declarations)), flush=True)
    if check_snapshot:
        print("All proof sources match the approved SHA256 snapshot", flush=True)
    return modules, declarations


def run(command, log_name):
    print("Running: " + " ".join(command), flush=True)
    result = subprocess.run(command, cwd=ROOT, text=True, encoding="utf-8",
                            errors="replace", stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (LOGS / log_name).write_text(result.stdout, encoding="utf-8")
    if result.returncode != 0 or re.search(r"\bwarning:", result.stdout):
        print(result.stdout[-6000:], file=sys.stderr)
        raise RuntimeError("Command failed or produced a warning; see .verification/" + log_name)
    return result.stdout


def check_axioms(output, expected):
    entries = re.findall(
        r"'(.+?)' (?:depends on axioms:\s*\[([\s\S]*?)\]|does not depend on any axioms)",
        output)
    found = [name for name, _ in entries]
    require(len(found) == len(set(found)), "Duplicate axiom audit result")
    require(set(found) == set(expected), "Axiom audit declaration list is incomplete")
    for name, axioms in entries:
        used = {axiom.strip() for axiom in axioms.split(",") if axiom.strip()}
        require(used <= ALLOWED_AXIOMS, "Unexpected axioms for " + name + ": " + str(used))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-build", action="store_true",
                        help="Use only immediately after a successful lake build (for CI)")
    parser.add_argument("--check-snapshot", action="store_true",
                        help="Also require exact agreement with the approved source hashes")
    args = parser.parse_args()
    modules, declarations = sources_and_declarations(args.check_snapshot)
    LOGS.mkdir(exist_ok=True)
    if not args.skip_build:
        run(["lake", "build"], "build.log")

    generated = LOGS / "FullAudit.lean"
    generated.write_text("\n".join(
        ["import " + module for module in modules] + [""] +
        ["#print axioms " + name for name in declarations] + [""]), encoding="utf-8")
    output = run(["lake", "env", "lean", "-DautoImplicit=false",
                  "--root=.verification", ".verification/FullAudit.lean"], "full-audit.log")
    check_axioms(output, declarations)

    output = run(["lake", "env", "lean", "-DautoImplicit=false",
                  "audits/MainAudit.lean"], "main-audit.log")
    main_names = re.findall(r"^#print axioms\s+(\S+)",
                            (ROOT / "audits/MainAudit.lean").read_text(encoding="utf-8"), re.M)
    require("StrongSpherical.main_theorem" in main_names, "Main theorem missing from audit")
    require("StrongSpherical.strong_spherical_maximal_bound" in main_names,
            "Expanded main theorem missing from audit")
    check_axioms(output, main_names)
    print("PASS: {} source declarations and the exact main theorem audited; "
          "only standard Lean axioms allowed".format(len(declarations)), flush=True)
    print("Logs: .verification/", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        sys.exit(1)
