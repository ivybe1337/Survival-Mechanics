"""
Run the reproduction scripts cited in the paper and write MANIFEST.json with each receipt's SHA-256 digest
and pass flag. Usage:  python3 run_release.py   (from this directory)
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
JOBS = [
    # (script, receipt json, working dir)
    ("base/proof_calculations.py", "base/la_synthetic_receipt.json", "base"),
    ("base/sperner_receipt.py", "base/sperner_receipt.json", "base"),
    ("base/lipschitz_receipt.py", "base/lipschitz_receipt.json", "base"),
    ("base/presentation_receipt.py", "base/presentation_receipt.json", "base"),
    ("base/mixed_objective_receipt.py", "base/mixed_objective_receipt.json", "base"),
    ("base/value_function_receipt.py", "base/value_function_receipt.json", "base"),
    ("base/nfa_noncanonicity_receipt.py", "base/nfa_noncanonicity_receipt.json", "base"),
    ("r1_joint_state.py", "r1_joint_state.json", "."),
    ("r2_survival_conditioned.py", "r2_survival_conditioned.json", "."),
    ("r3_approximate_value.py", "r3_approximate_value.json", "."),
    ("r4_certificate_dimension.py", "r4_certificate_dimension.json", "."),
    ("r5_presentations.py", "r5_presentations.json", "."),
    ("r6_feasible_sets_and_hmm.py", "r6_feasible_sets_and_hmm.json", "."),
    ("r7_visited_futures.py", "r7_visited_futures.json", "."),
]

manifest = {}
ok = True
for script, receipt, wd in JOBS:
    cwd = os.path.join(HERE, wd)
    r = subprocess.run([sys.executable, os.path.basename(script)], cwd=cwd, capture_output=True, text=True)
    with open(os.path.join(HERE, receipt)) as fh:
        data = json.load(fh)
    flags, viol = [], []

    def walk(o):
        if isinstance(o, dict):
            for k, v in o.items():
                kl = k.lower()
                if isinstance(v, bool) and ("pass" in kl or kl.endswith("_ok") or "match" in kl):
                    flags.append(v)
                if isinstance(v, int) and not isinstance(v, bool) and "violation" in kl:
                    viol.append(v)
                walk(v)
        elif isinstance(o, list):
            for v in o:
                walk(v)
    walk(data)
    passed = (r.returncode == 0) and all(flags) and all(v == 0 for v in viol) and (len(flags) + len(viol) > 0)
    manifest[script] = {"receipt": receipt, "exit_code": r.returncode, "all_checks_pass": bool(passed),
                        "sha256": data["receipt_sha256_without_hash_field"]}
    ok &= (r.returncode == 0) and bool(passed)
    print(f"{script:45s} exit={r.returncode} pass={passed} sha256={data['receipt_sha256_without_hash_field'][:16]}...")

with open(os.path.join(HERE, "MANIFEST.json"), "w") as fh:
    json.dump({"all_ok": ok, "receipts": manifest}, fh, indent=2, sort_keys=True)
print("ALL OK" if ok else "SOMETHING FAILED")
sys.exit(0 if ok else 1)
