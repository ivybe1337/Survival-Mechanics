"""Receipt G generator for T17 (a complete necessary-and-sufficient
characterization of decision sufficiency for U1's general/mixed-objective
case). Integer arithmetic only, no floats, no randomness, fully
deterministic.

Survival rule reused throughout this paper: a trace survives iff it never
contains the substring "bb". Alphabet Sigma = {a,b}. H = Sigma* (every
extension legal, so T11's totalization holds trivially).

epsilon(h) := |h| mod 2 -- a simple, genuinely non-constant predictive
state used only for this receipt, chosen because it lets two DIFFERENT
histories ("" and "aa") share the same epsilon value without being equal.

This script checks:
  1. kappa via raw residual rows (independent of any shortcut), matching
     the 3-state structure used elsewhere in this paper.
  2. Part (a) [sufficiency]: for a reward that factors through J=(eps,kappa)
     via R(h,e) = f(eps(h), kappa(h+e), e) -- i.e. genuinely using the
     POST-EXTENSION kappa class, which T13's original hypothesis did not
     allow -- a*(h) depends only on J(h), checked exhaustively over every
     pair of histories (of length <=5) with matching J.
  3. Part (b) [necessity/tightness]: an explicit reward NOT of the form
     R(h,e)=R~(J(h),e) -- literally keyed to the raw identity of h -- for
     which two histories with identical J give DIFFERENT optimal actions,
     confirming the "factors through J" hypothesis in Part (a) cannot be
     dropped in general.
"""
from __future__ import annotations
import json, hashlib
from pathlib import Path
from itertools import product

OUT = Path(__file__).with_name("mixed_objective_receipt.json")
ALPHA = ("a", "b")
N = 5  # exhaustive test depth for histories


def survives(w: str) -> bool:
    return "bb" not in w


def words_upto(alpha, max_len):
    yield ""
    for n in range(1, max_len + 1):
        for tup in product(alpha, repeat=n):
            yield "".join(tup)


# ---------------------------------------------------------------------
# kappa via raw residual rows (ground truth, independent of shortcuts).
# ---------------------------------------------------------------------
SUFFIX_HORIZON = 8

def raw_row(h: str):
    return tuple(int(survives(h + z)) for z in words_upto(ALPHA, SUFFIX_HORIZON))

test_histories = list(words_upto(ALPHA, N))
all_histories_plus_one = list(words_upto(ALPHA, N + 1))  # covers h+e for h up to length N
raw_rows = {h: raw_row(h) for h in all_histories_plus_one}


def kappa(h: str):
    return raw_rows[h]  # the row itself is a faithful representative of kappa(h)


def epsilon(h: str) -> int:
    return len(h) % 2


def J(h: str):
    return (epsilon(h), kappa(h))


# A(h) = {e in Sigma : R_V(he) != empty}. For this monotonic rule,
# R_V(he) != empty iff survives(he) (see paper's own T13/T15 discussion).
def A(h: str):
    return frozenset(e for e in ALPHA if survives(h + e))


# ---------------------------------------------------------------------
# Part (a): reward factoring through J via the post-extension kappa class.
# f is deliberately chosen to depend on kappa(h+e) in a way T13's original
# hypothesis (reward depends on epsilon(h) and e only) could not express.
# ---------------------------------------------------------------------
def f_reward(eps_h, kappa_he, e):
    # kappa_he is a row-tuple; use its "deadness" (all-zero row) and eps_h
    # and e to build a concrete numeric reward.
    is_dead = 1 if all(x == 0 for x in kappa_he) else 0
    return eps_h * 10 - is_dead * 5 + (1 if e == "a" else 0)


def R_partA(h: str, e: str):
    return f_reward(epsilon(h), kappa(h + e), e)


def astar(h: str, R):
    feas = A(h)
    if not feas:
        return frozenset()
    best = max(R(h, e) for e in feas)
    return frozenset(e for e in feas if R(h, e) == best)


# Exhaustive check: for every pair (h, h') with J(h) == J(h'), confirm
# astar(h) == astar(h') under R_partA.
J_groups = {}
for h in test_histories:
    J_groups.setdefault(J(h), []).append(h)

part_a_violations = []
part_a_pairs_checked = 0
for j, group in J_groups.items():
    for i in range(len(group)):
        for k in range(i + 1, len(group)):
            h, hp = group[i], group[k]
            part_a_pairs_checked += 1
            a1, a2 = astar(h, R_partA), astar(hp, R_partA)
            if a1 != a2:
                part_a_violations.append({"h": h, "hp": hp, "J": [j[0], "row"], "astar_h": sorted(a1), "astar_hp": sorted(a2)})

part_a_ok = len(part_a_violations) == 0

# Also confirm A(h) itself matches J (feasibility determined by kappa alone,
# per T13(a)) across the same groups, as a sanity cross-check.
feasibility_violations = []
for j, group in J_groups.items():
    for i in range(len(group)):
        for k in range(i + 1, len(group)):
            h, hp = group[i], group[k]
            if A(h) != A(hp):
                feasibility_violations.append([h, hp])
feasibility_ok = len(feasibility_violations) == 0


# ---------------------------------------------------------------------
# Part (b): necessity/tightness counterexample.
# h = "", hp = "aa": same kappa (both class "A": safe, empty or ends in
# 'a'), same epsilon (|""|=0, |"aa"|=2, both even). A reward keyed to the
# raw identity of h (not factoring through J) breaks sufficiency.
# ---------------------------------------------------------------------
H_WITNESS = ""
HP_WITNESS = "aa"

def R_partB(h: str, e: str):
    if h == H_WITNESS and e == "a":
        return 1
    if h == HP_WITNESS and e == "b":
        return 1
    return 0

witness_J_equal = (J(H_WITNESS) == J(HP_WITNESS))
witness_astar_h = astar(H_WITNESS, R_partB)
witness_astar_hp = astar(HP_WITNESS, R_partB)
witness_astar_differ = (witness_astar_h != witness_astar_hp)
witness_A_h = A(H_WITNESS)
witness_A_hp = A(HP_WITNESS)
witness_feasible_sets_equal = (witness_A_h == witness_A_hp)

part_b_ok = witness_J_equal and witness_astar_differ and witness_feasible_sets_equal

receipt = {
    "receipt_G_mixed_objective_T17": {
        "alphabet": ALPHA,
        "survival_rule": "trace survives iff substring 'bb' never occurs",
        "epsilon_definition": "epsilon(h) := len(h) mod 2",
        "history_length_tested": N,
        "distinct_kappa_classes_in_test_set": len(set(raw_rows.values())),
        "part_a_sufficiency": {
            "pairs_checked": part_a_pairs_checked,
            "violations": part_a_violations,
            "sufficiency_holds": part_a_ok,
        },
        "feasibility_cross_check": {
            "violations": feasibility_violations,
            "feasibility_matches_kappa_alone": feasibility_ok,
        },
        "part_b_necessity_witness": {
            "h": H_WITNESS,
            "hp": HP_WITNESS,
            "epsilon_h": epsilon(H_WITNESS),
            "epsilon_hp": epsilon(HP_WITNESS),
            "J_h_equals_J_hp": witness_J_equal,
            "A_h": sorted(witness_A_h),
            "A_hp": sorted(witness_A_hp),
            "feasible_sets_equal": witness_feasible_sets_equal,
            "astar_h": sorted(witness_astar_h),
            "astar_hp": sorted(witness_astar_hp),
            "astar_differs": witness_astar_differ,
            "confirms_necessity": part_b_ok,
        },
        "all_checks_pass": part_a_ok and feasibility_ok and part_b_ok,
    }
}

raw = json.dumps(receipt, indent=2, sort_keys=True)
receipt["receipt_sha256_without_hash_field"] = hashlib.sha256(raw.encode()).hexdigest()
OUT.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")

print("part_a: pairs_checked =", part_a_pairs_checked, "sufficiency_holds =", part_a_ok)
print("feasibility_cross_check:", feasibility_ok)
print("part_b witness:", receipt["receipt_G_mixed_objective_T17"]["part_b_necessity_witness"])
print("all_checks_pass:", receipt["receipt_G_mixed_objective_T17"]["all_checks_pass"])
print("sha256:", receipt["receipt_sha256_without_hash_field"])
