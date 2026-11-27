#!/usr/bin/env python3
"""Count the open statements that are proved: python3 scripts/check_proofs.py

An open statement `KellerZero.Open.<Name>` (lean/KellerZero/Open.lean) counts as proved when
lean/KellerZero/Proofs/<Name>.lean builds and declares

    theorem KellerZero.Proofs.<Name> : KellerZero.Open.<Name>

using no axiom beyond propext, Classical.choice and Quot.sound (so no sorry). Needs Lean
(elan) and, once, `cd lean && lake exe cache get`. Prints one JSON line; exit code 0 unless a
proof file is present and refused.
"""
import json
import os
import re
import subprocess
import sys
import tempfile

NAMES = ["ImageIsComplementOfCurve", "ReductionMapIsKeller", "QuadraticKellerMapsAreInjective",
         "CubicGadgetIsKeller", "QuadraticKellerMapsAreBijective", "FibreCount",
         "WitnessIsSound", "RefutationOfMap"]
# The chain that is checked already: each must build and rest on the three axioms only.
CHECKED = ["det_jacobian", "jacobian_conjecture_fails_dim_three", "fibre_zero", "omitted_curve",
           "exists_zero_reductionMap_iff_satisfiable", "hitsTarget_iff_satisfiable",
           "mem_fibre_iff_simple_root", "image_complex", "image_real", "scaling",
           "cubic_fibre", "cubicPoly_not_injective", "threeSAT_reduces_to_keller_zero",
           "pderiv_bind₁", "det_wireExt", "det_cubic10Map", "totalDegree_cubic10Map",
           "cubic10Map_not_injective", "det_cubic11Map", "totalDegree_cubic11Map",
           "cubic11Map_not_injective", "threeSAT_reduces_to_cubic_keller_zero",
           "keller_zero_hard_exactly_from_degree_three", "curve_certificate", "not_on_curve",
           "target_certificate", "zeros_of_H", "det_jacobian_bilinearMap", "refutation_of_formula"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LEAN = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean")


def run(cmd):
    return subprocess.run(cmd, cwd=LEAN, capture_output=True, text=True)


def axioms(text, name):
    """The axioms `#print axioms` reported for `name`, or None when it reported nothing."""
    if "'%s' does not depend on any axioms" % name in text:
        return set()
    m = re.search(r"'%s' depends on axioms: \[([^\]]*)\]" % re.escape(name), text)
    return None if not m else set(a.strip() for a in m.group(1).split(","))


def chain():
    """Why the checked chain is not sound, or None."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write("import KellerZero\n" + "".join("#print axioms KellerZero.%s\n" % n for n in CHECKED))
        path = f.name
    try:
        out = run(["lake", "env", "lean", path])
    finally:
        os.unlink(path)
    text = out.stdout + out.stderr
    if out.returncode != 0:
        return "the checked chain does not build: " + text.strip()[-600:]
    for n in CHECKED:
        used = axioms(text, "KellerZero." + n)
        if used is None or used - ALLOWED:
            return "KellerZero.%s: %s" % (n, "no axiom report" if used is None else "axioms " + ", ".join(sorted(used - ALLOWED)))
    return None


def judge(name):
    built = run(["lake", "build", "KellerZero.Proofs." + name])
    if built.returncode != 0:
        return "does not build: " + (built.stdout + built.stderr).strip()[-600:]
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write("import KellerZero.Proofs.%s\n" % name)
        f.write("example : KellerZero.Open.%s := KellerZero.Proofs.%s\n" % (name, name))
        f.write("#print axioms KellerZero.Proofs.%s\n" % name)
        path = f.name
    try:
        out = run(["lake", "env", "lean", path])
    finally:
        os.unlink(path)
    text = out.stdout + out.stderr
    if out.returncode != 0:
        return "KellerZero.Proofs.%s is not a proof of KellerZero.Open.%s: %s" % (name, name, text.strip()[-600:])
    used = axioms(text, "KellerZero.Proofs." + name)
    if used is None:
        return "could not read the axioms: " + text.strip()[-300:]
    extra = sorted(used - ALLOWED)
    return ("uses axioms that are not allowed: " + ", ".join(extra)) if extra else None


def main():
    proved, refused = [], {}
    broken = chain()
    if broken:
        refused["checked chain"] = broken
    for name in NAMES:
        if not os.path.exists(os.path.join(LEAN, "KellerZero", "Proofs", name + ".lean")):
            continue
        why = judge(name)
        if why is None:
            proved.append(name)
        else:
            refused[name] = why
    print(json.dumps({"ok": not refused, "checked_chain": 0 if broken else len(CHECKED),
                      "open_statements_proved": len(proved), "of": len(NAMES),
                      "proved": proved, "refused": refused}))
    return 1 if refused else 0


if __name__ == "__main__":
    sys.exit(main())
