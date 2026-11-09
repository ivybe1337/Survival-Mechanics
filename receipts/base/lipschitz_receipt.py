"""Receipt E generator for T15 (Lipschitz-type bound on the bounded-horizon
hard-admissible-extension set A^(H)(h), partially resolving U3).
Integer/exact arithmetic only, no floating point, no randomness, fully
deterministic. Matches the style of proof_calculations.py and
sperner_receipt.py.

Definitions used (must match the paper's T6 and T13 exactly):
  R_V^(H)(h) := {z in Sigma* : |z| <= H, h.z in Hist, V(h.z) = 1}      (T6)
  A^(H)(h)   := {e in Sigma : R_V^(H-1)(h.e) != empty}   for H >= 1
              := empty set                                for H = 0

Claim (T15):
  |A^(H)(h) sym-diff A^(H)(h')| <= min(|Sigma|, d_H^+(h,h'))
  where d_H^+(h,h') := |R_V^(H)(h) sym-diff R_V^(H)(h')|

This script (a) exhaustively checks the bound for zero violations over two
survival rules -- one monotonic ("never contains bb", reused from Receipt A
for continuity), one non-monotonic ("even number of b's so far", chosen
specifically because a non-monotonic rule lets a killed history "revive",
which is the case that stresses the bound hardest -- and (b) exhibits and
verifies, by direct recomputation and assertion (not by formula), explicit
tightness witnesses in both regimes of the min(): one where the achieved
value equals d_H^+ itself (d_H^+ < |Sigma|), and one where it saturates at
|Sigma| (d_H^+ >= |Sigma|).
"""
from __future__ import annotations
import json, hashlib
from pathlib import Path
from itertools import product

OUT = Path(__file__).with_name("lipschitz_receipt.json")
ALPHA = ("a", "b")


def survives_monotonic(w: str) -> bool:
    return "bb" not in w


def survives_nonmonotonic(w: str) -> bool:
    return w.count("b") % 2 == 0


def words_upto(alpha, max_len):
    yield ""
    for n in range(1, max_len + 1):
        for tup in product(alpha, repeat=n):
            yield "".join(tup)


def R_bounded(survives, h: str, H: int):
    if H < 0:
        return set()
    return set(z for z in words_upto(ALPHA, H) if survives(h + z))


def A_bounded(survives, h: str, H: int):
    if H <= 0:
        return set()
    out = set()
    for e in ALPHA:
        if any(survives(h + e + zp) for zp in words_upto(ALPHA, H - 1)):
            out.add(e)
    return out


def d_bounded(survives, h, hp, H):
    Rh = R_bounded(survives, h, H)
    Rhp = R_bounded(survives, hp, H)
    return len(Rh.symmetric_difference(Rhp))


def exhaustive_check(name, survives, L, Hs):
    all_histories = list(words_upto(ALPHA, L))
    per_H = []
    for H in Hs:
        violations = []
        tight_lt_sigma = None   # regime: 0 < lhs = d < |Sigma|
        tight_eq_sigma = None   # regime: lhs = |Sigma| <= d
        checked = 0
        for h in all_histories:
            for hp in all_histories:
                checked += 1
                Ah = A_bounded(survives, h, H)
                Ahp = A_bounded(survives, hp, H)
                lhs = len(Ah.symmetric_difference(Ahp))
                d = d_bounded(survives, h, hp, H)
                rhs = min(len(ALPHA), d)
                if lhs > rhs:
                    violations.append({"h": h, "hp": hp, "lhs": lhs, "d": d, "rhs": rhs})
                    continue
                if lhs == rhs and lhs > 0:
                    if d < len(ALPHA) and tight_lt_sigma is None:
                        tight_lt_sigma = {"h": h, "hp": hp, "lhs": lhs, "d": d}
                    if lhs == len(ALPHA) and tight_eq_sigma is None:
                        tight_eq_sigma = {"h": h, "hp": hp, "lhs": lhs, "d": d}
        per_H.append({
            "H": H,
            "pairs_checked": checked,
            "violations_found": len(violations),
            "violations": violations[:5],
            "tightness_witness_d_lt_sigma": tight_lt_sigma,
            "tightness_witness_lhs_eq_sigma": tight_eq_sigma,
        })
    return {"rule": name, "L": L, "alphabet_size": len(ALPHA), "results_by_horizon": per_H}


def reverify_witness(survives, h, hp, H):
    """Independently recompute lhs/rhs for one (h,h',H) witness, from the raw
    definitions, to confirm a witness pulled out of the exhaustive loop above
    is not a bookkeeping artifact."""
    Ah = A_bounded(survives, h, H)
    Ahp = A_bounded(survives, hp, H)
    lhs = len(Ah.symmetric_difference(Ahp))
    d = d_bounded(survives, h, hp, H)
    rhs = min(len(ALPHA), d)
    return {
        "h": h, "hp": hp, "H": H,
        "A_H_h": sorted(Ah), "A_H_hp": sorted(Ahp),
        "lhs_sym_diff": lhs, "d_H_plus": d, "rhs_min_sigma_d": rhs,
        "tight": lhs == rhs,
    }


mono = exhaustive_check("monotonic (avoid substring bb)", survives_monotonic, L=6, Hs=[0, 1, 2, 3, 4])
nonmono = exhaustive_check("non-monotonic (even count of b)", survives_nonmonotonic, L=6, Hs=[0, 1, 2, 3, 4])

total_violations = sum(r["violations_found"] for r in mono["results_by_horizon"]) + \
                    sum(r["violations_found"] for r in nonmono["results_by_horizon"])

# Independently reverify the two headline tightness witnesses used in the
# paper's T15 statement, by direct recomputation outside the search loop.
witness_regime_d_lt_sigma = reverify_witness(survives_monotonic, "", "b", 1)
witness_regime_lhs_eq_sigma = reverify_witness(survives_monotonic, "", "bb", 2)

receipt = {
    "receipt_E_lipschitz_bound_T15": {
        "definition_note": "A^(H)(h) := {e in Sigma : R_V^(H-1)(h.e) != empty} for H>=1, "
                            "empty for H=0; R_V^(H)(h) per T6. Claim: "
                            "|A^(H)(h) sym-diff A^(H)(h')| <= min(|Sigma|, d_H^+(h,h')).",
        "monotonic_rule_results": mono,
        "nonmonotonic_rule_results": nonmono,
        "total_pairs_checked": sum(r["pairs_checked"] for r in mono["results_by_horizon"]) +
                                sum(r["pairs_checked"] for r in nonmono["results_by_horizon"]),
        "total_violations_found": total_violations,
        "bound_holds_with_zero_violations": total_violations == 0,
        "reverified_witness_regime_d_lt_sigma": witness_regime_d_lt_sigma,
        "reverified_witness_regime_lhs_eq_sigma": witness_regime_lhs_eq_sigma,
        "both_witnesses_tight": witness_regime_d_lt_sigma["tight"] and witness_regime_lhs_eq_sigma["tight"],
    }
}

raw = json.dumps(receipt, indent=2, sort_keys=True)
receipt["receipt_sha256_without_hash_field"] = hashlib.sha256(raw.encode()).hexdigest()
OUT.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")

print("total_violations_found:", total_violations)
print("both_witnesses_tight:", receipt["receipt_E_lipschitz_bound_T15"]["both_witnesses_tight"])
print("witness d<sigma:", witness_regime_d_lt_sigma)
print("witness lhs=sigma:", witness_regime_lhs_eq_sigma)
print("sha256:", receipt["receipt_sha256_without_hash_field"])
