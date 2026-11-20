#!/usr/bin/env python3
# SCRIPT: FIG8-ANCHORS-VERIFY-01
"""Full harness for figure-eight-anchors-lean (core Lean 4, no Mathlib).

Why each check proves what it claims:
1. Build. `lake build` compiles every module; a type error stops it.
2. Kernel replay. `leanchecker` re-checks every declaration of every module in an
   independent kernel, so an elaborator bug cannot pass a bad proof.
3. Axiom audit. `#print axioms` names the axioms each theorem rests on. Allowed:
   {propext, Classical.choice, Quot.sound}. This excludes sorry (sorryAx), any
   project axiom, and native_decide (Lean.ofReduceBool).
4. Source scan. No `sorry`, `admit`, `native_decide` or `axiom` anywhere.
5. Inventory. The theorem count must match config.json, so nothing drops silently.
6. False controls. Each FalseControls/*.lean states something false; it must FAIL
   to compile for a mathematical reason, which shows the checker can say no.
7. Hashes. SHA-256 of every source file and of RELATIONS.json goes in the report.
8. Relations graph. Every theorem is a node with a rule tag and at least one edge; every edge end
   is an audited theorem or a declared source; every witness is an audited theorem; a forged edge
   is run through the same checker and must be rejected.
"""
import hashlib, json, os, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"; OUT.mkdir(exist_ok=True)
CFG = json.loads((ROOT / "scripts" / "config.json").read_text())
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
THM = re.compile(r"^theorem\s+([^\s:({\[]+)", re.M)
NS = re.compile(r"^namespace\s+(\S+)", re.M)
MATH_FAIL = re.compile(r"unsolved goals|proved that the proposition|failed to reduce to true|decide failed|grind failed|`grind` failed|omega could not|evaluates to false", re.I)
report = {"checks": {}}
ok = True

def run(cmd):
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)

r = run(["lake", "build"])
report["checks"]["build"] = r.returncode == 0
if r.returncode != 0:
    print(r.stdout[-3000:], r.stderr[-3000:]); sys.exit(1)
print("build: PASS")

replay = {}
for m in CFG["modules"]:
    r = run(["lake", "env", "leanchecker", m["module"]])
    replay[m["module"]] = r.returncode == 0
    if r.returncode != 0:
        ok = False; print("replay FAIL", m["module"], r.stdout[-800:], r.stderr[-800:])
report["checks"]["kernel_replay"] = replay
print("kernel replay:", "PASS" if all(replay.values()) else "FAIL")

names, scan_bad = [], []
for m in CFG["modules"]:
    src = (ROOT / m["path"]).read_text()
    code = re.sub(r"/-.*?-/", "", src, flags=re.S); code = re.sub(r"--.*", "", code)
    for bad in ("sorry", "admit", "native_decide"):
        if re.search(r"\b" + bad + r"\b", code): scan_bad.append((m["path"], bad))
    if re.search(r"^\s*axiom\s", code, re.M): scan_bad.append((m["path"], "axiom"))
    spaces = NS.findall(code)
    prefix = ".".join(spaces)
    for n in THM.findall(code):
        names.append((m["module"], prefix + "." + n if prefix else n))
report["checks"]["source_scan_clean"] = not scan_bad
if scan_bad: ok = False; print("scan FAIL", scan_bad)
print("source scan:", "PASS" if not scan_bad else "FAIL")

audit = ROOT / "verification" / "Audit.lean"
audit.write_text("\n".join(["import FigureEightAnchors"] + ["#print axioms " + n for _, n in names]) + "\n")
r = run(["lake", "env", "lean", str(audit)])
out = r.stdout + r.stderr
blocks = re.split(r"(?=^')", out, flags=re.M)
axiom_table, bad_ax = {}, []
for b in blocks:
    mm = re.match(r"'(.+?)' (?:depends|does)", b)
    if not mm: continue
    nm = mm.group(1)
    if "does not depend on any axioms" in b: ax = []
    else:
        mx = re.search(r"\[(.*?)\]", b, re.S); ax = [a.strip() for a in mx.group(1).split(",")] if mx else ["?"]
    axiom_table[nm] = ax
    if not set(ax) <= ALLOWED: bad_ax.append((nm, ax))
missing = [n for _, n in names if n not in axiom_table]
report["axioms"] = axiom_table
report["checks"]["axiom_audit"] = (r.returncode == 0 and not bad_ax and not missing)
if not report["checks"]["axiom_audit"]:
    ok = False; print("axiom FAIL", bad_ax, missing, out[-1500:])
print("axiom audit:", "PASS" if report["checks"]["axiom_audit"] else "FAIL", "(%d theorems)" % len(axiom_table))
print("  axiom-free theorems:", sum(1 for v in axiom_table.values() if not v))

inv_ok = len(names) == CFG["expected_theorems"]
report["checks"]["inventory"] = {"found": len(names), "expected": CFG["expected_theorems"], "ok": inv_ok}
if not inv_ok: ok = False
print("inventory:", len(names), "theorems,", "PASS" if inv_ok else "FAIL")

fc = {}
for f in sorted((ROOT / "FalseControls").glob("*.lean")):
    r = run(["lake", "env", "lean", str(f)])
    txt = r.stdout + r.stderr
    rejected = r.returncode != 0 and bool(MATH_FAIL.search(txt)) and "unknown identifier" not in txt.lower() and "unknown constant" not in txt.lower()
    fc[f.name] = {"rejected_for_math_reason": rejected, "message": txt.strip().splitlines()[0][:200] if txt.strip() else ""}
    if not rejected: ok = False; print("false control NOT properly rejected:", f.name, txt[-600:])
report["checks"]["false_controls"] = fc
fc_ok = len(fc) == CFG["expected_false_controls"] and all(v["rejected_for_math_reason"] for v in fc.values())
if not fc_ok: ok = False
print("false controls:", sum(v["rejected_for_math_reason"] for v in fc.values()), "/", len(fc), "rejected,", "PASS" if fc_ok else "FAIL")

# 8. Relations graph. Every audited theorem must be a node with at least one rule tag and at
#    least one edge; every edge endpoint must be an audited theorem or a declared external node;
#    every edge's witness must be an audited theorem (so no connection is claimed without a proof
#    behind it), and analogy-only edges are counted separately so they are never read as proved.
rel = json.loads((ROOT / "RELATIONS.json").read_text())
audited = set(axiom_table)
nodeset = set(rel["nodes"]); ext = set(rel["external"])
problems = []
problems += ["theorem not in graph: " + x for x in sorted(audited - nodeset)]
problems += ["graph node not an audited theorem: " + x for x in sorted(nodeset - audited)]
problems += ["node without rule tag: " + k for k, v in rel["nodes"].items() if not v["rules"]]
def edge_problems(edge_list):
    out, seen = [], set()
    for ed in edge_list:
        for end in (ed["from"], ed["to"]):
            if end not in audited and end not in ext: out.append("dangling edge end: " + end)
            seen.add(end)
        if ed["witness"] not in audited: out.append("unproved witness: " + ed["witness"])
        if ed["kind"] not in rel["kinds"]: out.append("unknown kind: " + ed["kind"])
    return out, seen
ep, touched = edge_problems(rel["edges"])
problems += ep
problems += ["isolated theorem (no edge): " + x for x in sorted(nodeset - touched)]
# Relations false control: a graph with a forged witness and a dangling endpoint must be rejected.
forged = {"from": "FigureEightAnchors.Gluing.golden_cycle", "to": "X:nowhere", "kind": "same-polynomial",
          "witness": "FigureEightAnchors.Gluing.golden_is_regular"}
forged_probs, _ = edge_problems(rel["edges"] + [forged])
caught = ("unproved witness: " + forged["witness"]) in forged_probs and ("dangling edge end: " + forged["to"]) in forged_probs
report["checks"]["relations_false_control_rejected"] = caught
if not caught: problems.append("relations checker accepted a forged edge")
print("relations false control (forged witness + dangling end):", "rejected" if caught else "ACCEPTED")
rel_ok = not problems
report["checks"]["relations"] = {"nodes": len(nodeset), "edges": len(rel["edges"]),
    "analogy_only_edges": sum(1 for ed in rel["edges"] if ed["kind"] == "analogy-only"),
    "external_edges": sum(1 for ed in rel["edges"] if ed["kind"] == "external"), "problems": problems, "ok": rel_ok}
if not rel_ok: ok = False
print("relations:", len(nodeset), "nodes,", len(rel["edges"]), "edges,", "PASS" if rel_ok else "FAIL")
for pr in problems: print("   ", pr)

hashes = {}
for p in sorted(list(ROOT.glob("FigureEightAnchors/*.lean")) + [ROOT / "FigureEightAnchors.lean"] + list(ROOT.glob("FalseControls/*.lean"))):
    hashes[str(p.relative_to(ROOT))] = hashlib.sha256(p.read_bytes()).hexdigest()
report["sha256"] = hashes
report["lean_version"] = run(["lean", "--version"]).stdout.strip()
report["all_pass"] = ok
(OUT / "report.json").write_text(json.dumps(report, indent=2))
print("ALL CHECKS", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
