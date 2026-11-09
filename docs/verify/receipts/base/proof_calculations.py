#!/usr/bin/env python3
"""Finite exact calculations used as receipts for the Likely and Allowed manuscript.
No learned model, sampling, or approximate arithmetic is used.
"""
from __future__ import annotations
from itertools import product
from fractions import Fraction
import json, hashlib
from pathlib import Path

OUT = Path(__file__).with_name("la_synthetic_receipt.json")


def words(alpha, max_len):
    yield ""
    for n in range(1, max_len + 1):
        for tup in product(alpha, repeat=n):
            yield "".join(tup)

# Example A: residual survival language. A complete trace survives iff it contains no 'bb'.
ALPHA = ("a", "b")
H = list(words(ALPHA, 4))
SUFFIX = list(words(ALPHA, 4))

def survives_global(w: str) -> bool:
    return "bb" not in w

def row(h: str):
    return tuple(int(survives_global(h + z)) for z in SUFFIX)

rows = {h: row(h) for h in H}
classes = {}
for h, r in rows.items():
    classes.setdefault(r, []).append(h)
# classify only viable histories separately from already-dead prefix; still exact matrix includes dead row.
class_ids = {r:i for i, r in enumerate(sorted(classes, key=lambda r: (sum(r), r)))}
h_to_class = {h: class_ids[r] for h,r in rows.items()}

# right congruence within the finite horizon where extensions/suffixes remain inside the tested truncation.
# To avoid horizon-edge artifacts, test rows with remaining suffix budget 3 after one-symbol extension.
SUFFIX3 = list(words(ALPHA, 3))
def row3(h): return tuple(int(survives_global(h+z)) for z in SUFFIX3)
pairs_checked = 0
right_congruence_ok = True
counterexample = None
H3 = list(words(ALPHA, 3))
for i,h in enumerate(H3):
    for hp in H3[i+1:]:
        if row3(h) != row3(hp):
            continue
        for e in ALPHA:
            # after extension compare remaining horizon 2
            S2 = list(words(ALPHA,2))
            rr1 = tuple(int(survives_global(h+e+z)) for z in S2)
            rr2 = tuple(int(survives_global(hp+e+z)) for z in S2)
            pairs_checked += 1
            if rr1 != rr2:
                right_congruence_ok = False
                counterexample = [h,hp,e]
                break
        if not right_congruence_ok: break
    if not right_congruence_ok: break

# Example B: epsilon and kappa partitions are incomparable in general.
# Histories p,q: same survival set but different predictive distributions -> kappa same, epsilon different.
# Histories r,s: same predictive distributions but different survival set -> epsilon same, kappa different.
futures = ("x","y")
predictive = {
    "p": (Fraction(9,10), Fraction(1,10)),
    "q": (Fraction(1,10), Fraction(9,10)),
    "r": (Fraction(1,2), Fraction(1,2)),
    "s": (Fraction(1,2), Fraction(1,2)),
}
survival = {
    "p": (1,1),
    "q": (1,1),
    "r": (1,0),
    "s": (0,1),
}

def partition(mapping):
    groups = {}
    for h,v in mapping.items(): groups.setdefault(tuple(v), []).append(h)
    return sorted([sorted(g) for g in groups.values()])

epsilon_partition = partition(predictive)
kappa_partition = partition(survival)

# Joint partition by ordered pair is coarsest common refinement in this finite example.
joint = {h:(predictive[h], survival[h]) for h in predictive}
joint_partition = partition(joint)

# Example C: minimal nogoods reconstruct a finite downward-closed admissibility complex.
# Universe {1,2,3,4}; forbidden minimal sets {1,2}, {3,4}. Admissible iff contains neither.
U = (1,2,3,4)
minimal_nogoods = [frozenset((1,2)), frozenset((3,4))]
subsets=[]
for mask in range(1<<len(U)):
    subsets.append(frozenset(U[i] for i in range(len(U)) if mask & (1<<i)))
admissible = [s for s in subsets if not any(m <= s for m in minimal_nogoods)]
# Recover minimal nonfaces from admissible membership.
nonfaces = [s for s in subsets if s not in admissible]
recovered = []
for s in nonfaces:
    if all(t in admissible for t in subsets if t < s):
        recovered.append(s)
recovered = sorted(recovered, key=lambda s:(len(s),tuple(sorted(s))))

receipt = {
  "example_A_residual_language": {
    "alphabet": ALPHA,
    "survival_rule": "trace survives iff substring 'bb' never occurs",
    "history_count": len(H),
    "suffix_count": len(SUFFIX),
    "distinct_rows": len(classes),
    "representative_classes": [sorted(v)[:12] for _,v in sorted(classes.items(), key=lambda kv: class_ids[kv[0]])],
    "right_congruence_checks": pairs_checked,
    "right_congruence_ok": right_congruence_ok,
    "counterexample": counterexample,
  },
  "example_B_epsilon_kappa_incomparability": {
    "futures": futures,
    "predictive_distributions": {h:[str(x) for x in v] for h,v in predictive.items()},
    "survival_rows": survival,
    "epsilon_partition": epsilon_partition,
    "kappa_partition": kappa_partition,
    "joint_partition": joint_partition,
    "witness_kappa_same_epsilon_different": ["p","q"],
    "witness_epsilon_same_kappa_different": ["r","s"],
  },
  "example_C_minimal_nogoods": {
    "universe": U,
    "declared_minimal_nogoods": [sorted(x) for x in minimal_nogoods],
    "admissible_count": len(admissible),
    "recovered_minimal_nonfaces": [sorted(x) for x in recovered],
    "exact_reconstruction": set(recovered) == set(minimal_nogoods),
  }
}
raw=json.dumps(receipt,indent=2,sort_keys=True)
receipt["receipt_sha256_without_hash_field"] = hashlib.sha256(raw.encode()).hexdigest()
OUT.write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
print(OUT)
print(json.dumps(receipt,indent=2,sort_keys=True))
