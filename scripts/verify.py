#!/usr/bin/env python3
r"""Verification for the free_markov package.

Steps:
  1. `lake build` of the stage libraries (exit code must be 0);
  2. `sorry` scan of the library sources and of the build log;
  3. axiom report for every declaration of the stage libraries (allowed:
     propext, Classical.choice, Quot.sound);
  4. for every public theorem, the cited-result hypotheses (structures listed in
     CITED below) that occur in its type.
  5. compilation of the trial files in `stage N/trial/` (not part of the library);
  6. the blueprint `formalization/blueprint/src/content.tex`: unique labels,
     every \uses resolves, acyclic dependency graph, every \lean name is a
     declaration of the built libraries.

Usage:  python3 scripts/verify.py [--stage 0] [--report PATH]
The toolchain is taken from $LAKE, else `lake` on PATH, else the elan toolchain
named in `lean-toolchain` under ~/.elan.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Structures that hold cited results (PLAN.md, Section 2).  Added by later stages.
CITED = ["FreeMarkov.JoyalStreet", "FreeMarkov.Strictification"]
STAGES = {
    0: ("FreeMarkovStage0", "FreeMarkov.Stage0", "stage 0"),
    1: ("FreeMarkovStage1", "FreeMarkov.Stage1", "stage 1"),
    2: ("FreeMarkovStage2", "FreeMarkov.Stage2", "stage 2"),
    3: ("FreeMarkovStage3", "FreeMarkov.Stage3", "stage 3"),
    4: ("FreeMarkovStage4", "FreeMarkov.Stage4", "stage 4"),
    5: ("FreeMarkovStage5", "FreeMarkov.Stage5", "stage 5"),
}


def find_lake() -> str:
    if os.environ.get("LAKE"):
        return os.environ["LAKE"]
    on_path = shutil.which("lake")
    if on_path:
        return on_path
    tc = (ROOT / "lean-toolchain").read_text().strip()
    folder = tc.replace("/", "--").replace(":", "---")
    for home in (Path.home() / ".elan",):
        cand = home / "toolchains" / folder / "bin" / "lake"
        if cand.exists():
            return str(cand)
    sys.exit("verify: no lake found (set $LAKE)")


def run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, **kw)


SORRY_RE = re.compile(r"\bsorry\b")


def strip_comments(src: str) -> str:
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    return re.sub(r"--[^\n]*", "", src)


def sorry_scan(folder: Path) -> list[str]:
    hits = []
    for p in sorted(folder.rglob("*.lean")):
        code = strip_comments(p.read_text())
        for i, line in enumerate(code.splitlines(), 1):
            if SORRY_RE.search(line):
                hits.append(f"{p.relative_to(ROOT)}: {line.strip()}")
    return hits


AXIOM_SCRIPT = r"""
import {root}
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let cited : List Name := [{cited}]
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`{prefix}).isPrefixOf mod do continue
    if n.isInternalDetail then continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .axiomInfo _ => "axiom"
      | _ => "other"
    let used := ci.type.getUsedConstants
    let hyps := cited.filter used.contains
    out := out.push s!"{{n}}\t{{kind}}\t{{mod}}\t{{String.intercalate "," (axs.toList.map toString)}}\t{{String.intercalate "," (hyps.map toString)}}"
  logInfo (String.intercalate "\n" out.toList)
"""


def axiom_report(lake: str, root_module: str, prefix: str) -> list[dict]:
    scratch = ROOT / ".scratch" / "verify"
    scratch.mkdir(parents=True, exist_ok=True)
    f = scratch / f"Axioms_{prefix.replace('.', '_')}.lean"
    cited = ", ".join(f"`{c}" for c in CITED)
    f.write_text(AXIOM_SCRIPT.format(root=root_module, prefix=prefix, cited=cited))
    r = run([lake, "env", "lean", str(f)])
    if r.returncode != 0:
        print(r.stdout, r.stderr)
        sys.exit("verify: axiom report failed")
    rows = []
    for line in r.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) != 5:
            continue
        name, kind, mod, axs, hyps = parts
        name = name.split(": ", 1)[-1] if ": " in name and "info" in name else name
        rows.append({
            "name": name, "kind": kind, "module": mod,
            "axioms": [a for a in axs.split(",") if a],
            "cited": [h for h in hyps.split(",") if h],
        })
    return rows


BLUEPRINT = ROOT / "formalization" / "blueprint" / "src" / "content.tex"
ENV_RE = re.compile(r"\\begin\{(definition|lemma|theorem|proposition|corollary|remark)\}(.*?)"
                    r"\\end\{\1\}(\s*\\begin\{proof\}(.*?)\\end\{proof\})?", re.S)


def blueprint_check(declarations: set[str]) -> list[str]:
    """Return a list of problems with the blueprint (empty if none)."""
    if not BLUEPRINT.exists():
        return [f"missing {BLUEPRINT.relative_to(ROOT)}"]
    tex = re.sub(r"(?m)^%.*$", "", BLUEPRINT.read_text())
    nodes: dict[str, dict] = {}
    problems = []
    for m in ENV_RE.finditer(tex):
        block = m.group(2) + (m.group(4) or "")
        labels = re.findall(r"\\label\{([^}]+)\}", block)
        if len(labels) != 1:
            problems.append(f"block without exactly one label: {block[:60]!r}")
            continue
        lab = labels[0]
        if lab in nodes:
            problems.append(f"duplicate label {lab}")
        uses = [u.strip() for g in re.findall(r"\\uses\{([^}]+)\}", block) for u in g.split(",")]
        leans = [u.strip() for g in re.findall(r"\\lean\{([^}]+)\}", block) for u in g.split(",")]
        nodes[lab] = {"uses": uses, "lean": leans, "leanok": "\\leanok" in m.group(2)}
    for lab, n in nodes.items():
        for u in n["uses"]:
            if u not in nodes:
                problems.append(f"{lab}: unknown dependency {u}")
        for d in n["lean"]:
            if d not in declarations:
                problems.append(f"{lab}: \\lean name not in the library: {d}")
        if n["lean"] and not n["leanok"]:
            problems.append(f"{lab}: has \\lean but no \\leanok")
    state: dict[str, int] = {}

    def visit(lab: str) -> None:
        if state.get(lab) == 2:
            return
        if state.get(lab) == 1:
            problems.append(f"cycle through {lab}")
            return
        state[lab] = 1
        for u in nodes[lab]["uses"]:
            if u in nodes:
                visit(u)
        state[lab] = 2

    for lab in nodes:
        visit(lab)
    print(f"blueprint: {len(nodes)} nodes, {sum(len(n['uses']) for n in nodes.values())} edges, "
          f"{sum(n['leanok'] for n in nodes.values())} formalized")
    return problems


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", type=int, action="append")
    ap.add_argument("--report", default=str(ROOT / ".scratch" / "verify" / "report.json"))
    args = ap.parse_args()
    stages = args.stage or sorted(STAGES)
    lake = find_lake()
    ok = True

    print(f"toolchain: {run([lake, '--version']).stdout.strip()}")
    libs = [STAGES[s][0] for s in stages]
    b = run([lake, "build", *libs])
    print(f"build {' '.join(libs)}: exit code {b.returncode}")
    if b.returncode != 0:
        print(b.stdout[-4000:], b.stderr[-4000:])
        sys.exit(1)
    sorry_warnings = [l for l in b.stdout.splitlines() if "declaration uses `sorry`" in l
                      or "declaration uses 'sorry'" in l]

    report = {"stages": {}}
    for s in stages:
        lib, prefix, folder = STAGES[s]
        hits = sorry_scan(ROOT / folder / prefix.split(".")[0])
        rows = axiom_report(lake, prefix, prefix)
        bad = [r for r in rows if set(r["axioms"]) - ALLOWED_AXIOMS]
        with_cited = [r for r in rows if r["cited"] and r["kind"] == "theorem"]
        trials = []
        for t in sorted((ROOT / folder / "trial").glob("*.lean")) if (ROOT / folder / "trial").exists() else []:
            tr = run([lake, "env", "lean", str(t)])
            trials.append({"file": str(t.relative_to(ROOT)), "exit": tr.returncode,
                           "sorry": "sorry" in tr.stdout})
        print(f"\n== stage {s} ({lib})")
        print(f"declarations: {len(rows)} ({sum(r['kind'] == 'theorem' for r in rows)} theorems)")
        print(f"`sorry` in sources: {len(hits)}")
        for h in hits:
            print("   ", h)
        print(f"`sorry` warnings in build log: {len(sorry_warnings)}")
        print(f"declarations with axioms outside {sorted(ALLOWED_AXIOMS)}: {len(bad)}")
        for r in bad:
            print(f"    {r['name']}: {', '.join(r['axioms'])}")
        print(f"theorems using cited results: {len(with_cited)}")
        for r in with_cited:
            print(f"    {r['name']}: {', '.join(r['cited'])}")
        for t in trials:
            print(f"trial {t['file']}: exit {t['exit']}{' (sorry)' if t['sorry'] else ''}")
        ok = ok and not hits and not bad and not sorry_warnings and all(
            t["exit"] == 0 and not t["sorry"] for t in trials)
        report["stages"][s] = {"sorry": hits, "bad_axioms": bad, "cited": with_cited,
                               "trials": trials, "declarations": rows}

    all_decls = {r["name"] for st in report["stages"].values() for r in st["declarations"]}
    bp = blueprint_check(all_decls)
    for p in bp:
        print("    blueprint:", p)
    ok = ok and not bp
    report["blueprint"] = bp

    Path(args.report).parent.mkdir(parents=True, exist_ok=True)
    Path(args.report).write_text(json.dumps(report, indent=1))
    print(f"\nreport: {Path(args.report).relative_to(ROOT)}")
    print("RESULT:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
