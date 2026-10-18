#!/usr/bin/env python3
"""Reproduce every check of the NonNormality library. Writes logs and a report to verification/.

1. `lake build` with no warnings and no errors.
2. Kernel replay of every module with `leanchecker`.
3. Axiom audit: `#print axioms` for every public theorem and definition found in the sources;
   each must rest only on propext, Classical.choice, Quot.sound (no sorryAx, no native_decide,
   no project axioms).
4. No `sorry` token anywhere in library, checks or false controls (comments included), and no
   `axiom` declarations in the library.
5. Exact Apache-2.0 header on every library file.
6. False controls: every file in FalseControls/ must fail, for a mathematical reason.
7. checks/*.lean compile with warnings as errors.
8. Mathlib style: the Mathlib standard linter set on every module, `#lint` (declaration linters)
   and `lake exe lint-style`.
9. SHA-256 of every source file.
"""
from __future__ import annotations
import hashlib, json, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
HEADER = ["/-", "Copyright (c) 2026 Jeromie Beasley. All rights reserved.",
          "Released under Apache 2.0 license as described in the file LICENSE.",
          "Authors: Jeromie Beasley", "-/"]
LIB = sorted((ROOT / "NonNormality").glob("*.lean")) + [ROOT / "NonNormality.lean"]
DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?"
                     r"(theorem|lemma|def|structure)\s+([^\s:({\[]+)", re.M)
MATH_FAILURE = re.compile(r"unsolved goals|linarith failed|made no progress|"
                          r"failed to prove|decide failed|norm_num failed", re.I)
INFRA_FAILURE = re.compile(r"unknown (?:module|identifier|constant|namespace)|unexpected token|"
                           r"object file .* does not exist|invalid field", re.I)


def run(label, argv, ok_codes=(0,)):
    proc = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
    text = " ".join(argv) + "\n" + proc.stdout + proc.stderr
    (OUT / f"{label}.log").write_text(text)
    if proc.returncode not in ok_codes:
        print(text)
        raise SystemExit(f"{label}: exit code {proc.returncode}")
    return proc, text


def strip_comments(text):
    text = re.sub(r"/-.*?-/", lambda m: re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def declarations():
    names = []
    for path in LIB:
        text = strip_comments(path.read_text())
        ns = re.findall(r"^namespace\s+(\S+)", text, re.M)
        for kind, name in DECL_RE.findall(text):
            if path.name == "NonNormality.lean":
                continue
            names.append(f"{ns[0]}.{name}" if ns else name)
    return names


def main():
    OUT.mkdir(exist_ok=True)
    (OUT / "report.json").unlink(missing_ok=True)
    manifest = (ROOT / "lake-manifest.json").read_bytes()
    _, text = run("lean_version", ["lean", "--version"])
    _, build = run("build", ["lake", "build"])
    if re.search(r"warning|error", build.split("\n", 1)[1]):
        raise SystemExit("build reported warnings or errors")
    mods = ["NonNormality"] + [f"NonNormality.{p.stem}" for p in LIB if p.parent.name == "NonNormality"]
    for mod in mods:
        run(f"kernel_{mod}", ["lake", "env", "leanchecker", mod])
    files = LIB + sorted((ROOT / "checks").glob("*.lean")) + sorted((ROOT / "FalseControls").glob("*.lean"))
    for path in files:
        if re.search(r"\bsorry\b", path.read_text()):
            raise SystemExit(f"placeholder token in {path}")
    for path in LIB:
        if path.read_text().splitlines()[:5] != HEADER:
            raise SystemExit(f"license header missing in {path}")
        if re.search(r"^\s*axiom\s", strip_comments(path.read_text()), re.M):
            raise SystemExit(f"axiom declaration in {path}")
    names = declarations()
    audit = OUT / "AxiomAudit.lean"
    audit.write_text("import NonNormality\n" + "".join(f"#print axioms {n}\n" for n in names))
    _, axlog = run("axioms", ["lake", "env", "lean", str(audit.relative_to(ROOT))])
    axioms = {}
    for n, block in zip(names, re.split(r"(?m)^(?='[^']+' (?:depends on axioms|does not depend))",
                                        axlog.split("\n", 1)[1])[1:]):
        found = set(re.findall(r"[\w.]+", block.split("axioms:", 1)[1])) if "axioms:" in block else set()
        if f"'{n}'" not in block:
            raise SystemExit(f"axiom output out of order at {n}")
        if not found <= ALLOWED:
            raise SystemExit(f"{n} uses {found - ALLOWED}")
        axioms[n] = sorted(found)
    if len(axioms) != len(names):
        raise SystemExit(f"axiom audit covered {len(axioms)} of {len(names)} declarations")
    controls = {}
    for path in sorted((ROOT / "FalseControls").glob("*.lean")):
        proc, out = run(f"false_{path.stem}", ["lake", "env", "lean", str(path.relative_to(ROOT))],
                        ok_codes=(0, 1))
        if proc.returncode == 0 or not MATH_FAILURE.search(out) or INFRA_FAILURE.search(out):
            raise SystemExit(f"false control {path.name} did not fail for a mathematical reason")
        controls[path.name] = "rejected"
    for path in sorted((ROOT / "checks").glob("*.lean")):
        run(f"check_{path.stem}", ["lake", "env", "lean", "-DwarningAsError=true",
                                   str(path.relative_to(ROOT))])
    for path in LIB:
        _, out = run(f"stdlint_{path.stem}", ["lake", "env", "lean", "-Dlinter.mathlibStandardSet=true",
                                              str(path.relative_to(ROOT))])
        if "warning" in out.split("\n", 1)[1]:
            raise SystemExit(f"standard linter warnings in {path}")
    lint = OUT / "DeclarationLint.lean"
    lint.write_text("import NonNormality\nimport Mathlib.Tactic.Linter\n#lint in NonNormality\n")
    _, out = run("declaration_lint", ["lake", "env", "lean", str(lint.relative_to(ROOT))])
    if "All linting checks passed!" not in out:
        raise SystemExit("#lint reported problems")
    _, out = run("lint_style", ["lake", "exe", "lint-style", "NonNormality"])
    rest = out.split("\n", 1)[1].replace("warning: nolints file could not be read; treating as empty: "
                                         "scripts/nolints-style.txt", "").strip()
    if rest:
        print(out)
        raise SystemExit("lint-style reported problems")
    if manifest != (ROOT / "lake-manifest.json").read_bytes():
        raise SystemExit("manifest changed")
    kinds = {}
    for path in LIB:
        for kind, _ in DECL_RE.findall(strip_comments(path.read_text())):
            kinds[kind] = kinds.get(kind, 0) + 1
    report = {
        "lean": text.split("\n")[1].strip(),
        "mathlib": json.loads(manifest)["packages"][0]["rev"],
        "build": "passed, no warnings", "kernel_replay": mods,
        "declarations_audited": len(names), "declaration_kinds": kinds,
        "axioms": axioms, "false_controls": controls,
        "checks": [p.name for p in sorted((ROOT / "checks").glob("*.lean"))],
        "standard_lint": "passed", "declaration_lint": "passed", "lint_style": "passed",
        "sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
    }
    (OUT / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"All checks passed: {len(names)} declarations, {len(controls)} false controls rejected.")


if __name__ == "__main__":
    main()
