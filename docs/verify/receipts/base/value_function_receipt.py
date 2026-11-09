"""Receipt H generator for T18 (exact multi-step value-function sufficiency
of J=(epsilon,kappa) under a stated standing hypothesis that epsilon is
also right-congruent with an induced transition delta_epsilon -- a real,
proven, but explicitly partial step toward U3's actual ask, which is the
harder APPROXIMATE / policy-restricted bisimulation-metric bound; T18 does
NOT attempt that harder question and the paper says so explicitly).
Integer arithmetic only, no floats, no randomness, fully deterministic.

Survival rule reused throughout this paper: "avoid bb". Alphabet {a,b}.

epsilon(h) := len(h) mod 3, with the (trivially verified) induced
transition delta_epsilon(eps, e) := (eps + 1) mod 3 -- independent of e,
since every extension increases length by exactly 1 regardless of symbol,
so epsilon(h) = epsilon(h') implies epsilon(h+e) = epsilon(h'+e) for every
e: the standing hypothesis genuinely holds for this concrete epsilon, not
merely assumed.

kappa classification reuses the shortcut classifier already independently
verified against raw residual rows in Receipt F (states "A"/"B"/"D"), used
here only to DEFINE a concrete always-feasible policy pi and reward R; the
actual J-equality used to check sufficiency is computed from raw residual
rows directly (ground truth), not from the shortcut.
"""
from __future__ import annotations
import json, hashlib
from pathlib import Path
from itertools import product

OUT = Path(__file__).with_name("value_function_receipt.json")
ALPHA = ("a", "b")
N = 5           # exhaustive history-length bound for the J-matching search
MAX_STEPS = 6   # value-function horizons tested


def survives(w: str) -> bool:
    return "bb" not in w


def words_upto(alpha, max_len):
    yield ""
    for n in range(1, max_len + 1):
        for tup in product(alpha, repeat=n):
            yield "".join(tup)


# ---------------------------------------------------------------------
# kappa via raw residual rows (ground truth).
# ---------------------------------------------------------------------
SUFFIX_HORIZON = 8

def raw_row(h: str):
    return tuple(int(survives(h + z)) for z in words_upto(ALPHA, SUFFIX_HORIZON))

# Histories needed: up to length N for the J-matching search, but the
# value-function recursion walks forward up to MAX_STEPS more symbols from
# any such h, so raw rows must be available for histories up to
# N + MAX_STEPS.
MAXLEN = N + MAX_STEPS
all_histories = list(words_upto(ALPHA, MAXLEN))
raw_rows = {h: raw_row(h) for h in all_histories}


def kappa(h: str):
    return raw_rows[h]


def epsilon(h: str) -> int:
    return len(h) % 3


def J(h: str):
    return (epsilon(h), kappa(h))


def kappa_shortcut(h: str) -> str:
    if not survives(h):
        return "D"
    if h != "" and h[-1] == "b":
        return "B"
    return "A"


def A(h: str):
    return frozenset(e for e in ALPHA if survives(h + e))


# ---------------------------------------------------------------------
# Policy: always feasible, always alive-preserving, non-constant. From
# class "A" play 'b' (moves to B); from class "B" play 'a' (forced, only
# feasible choice anyway, moves back to A); undefined ("None") from dead
# class D, which this policy should provably never reach starting from a
# live history (checked below, not just assumed).
# ---------------------------------------------------------------------
def pi(h: str):
    cls = kappa_shortcut(h)
    if cls == "A":
        return "b"
    if cls == "B":
        return "a"
    return None  # dead; should never be invoked starting from a live h


def R_tilde(eps_h, e):
    return eps_h * 2 + (1 if e == "a" else 0)


def R(h, e):
    return R_tilde(epsilon(h), e)


def V(h: str, n: int, trace=None):
    """V_pi^n(h), raising if the policy is ever invoked on a dead history
    (which would indicate a design error in pi, not something to silently
    paper over)."""
    if n == 0:
        return 0
    e = pi(h)
    if e is None:
        raise RuntimeError(f"policy invoked on dead history {h!r} -- design error")
    if e not in A(h):
        raise RuntimeError(f"policy chose infeasible action {e!r} at {h!r} -- design error")
    return R(h, e) + V(h + e, n - 1)


# ---------------------------------------------------------------------
# Verification.
# ---------------------------------------------------------------------
test_histories = list(words_upto(ALPHA, N))
live_histories = [h for h in test_histories if survives(h)]

J_groups = {}
for h in live_histories:
    J_groups.setdefault(J(h), []).append(h)

violations = []
pairs_checked = 0
policy_errors = []
for n in range(0, MAX_STEPS + 1):
    for j, group in J_groups.items():
        for i in range(len(group)):
            for k in range(i + 1, len(group)):
                h, hp = group[i], group[k]
                pairs_checked += 1
                try:
                    v1 = V(h, n)
                    v2 = V(hp, n)
                except RuntimeError as ex:
                    policy_errors.append(str(ex))
                    continue
                if v1 != v2:
                    violations.append({"n": n, "h": h, "hp": hp, "V_h": v1, "V_hp": v2})

sufficiency_holds = (len(violations) == 0) and (len(policy_errors) == 0)

# Cross-check the standing hypothesis on epsilon directly and exhaustively:
# epsilon(h) == epsilon(h') implies epsilon(h+e) == epsilon(h'+e) for every
# e, over all tested pairs.
eps_hypothesis_violations = []
eps_groups = {}
for h in test_histories:
    eps_groups.setdefault(epsilon(h), []).append(h)
for eps_val, group in eps_groups.items():
    for i in range(len(group)):
        for k in range(i + 1, len(group)):
            h, hp = group[i], group[k]
            for e in ALPHA:
                if epsilon(h + e) != epsilon(hp + e):
                    eps_hypothesis_violations.append([h, hp, e])
eps_hypothesis_holds = len(eps_hypothesis_violations) == 0

receipt = {
    "receipt_H_value_function_sufficiency_T18": {
        "alphabet": ALPHA,
        "survival_rule": "trace survives iff substring 'bb' never occurs",
        "epsilon_definition": "epsilon(h) := len(h) mod 3",
        "delta_epsilon_definition": "delta_epsilon(eps, e) := (eps + 1) mod 3, independent of e",
        "history_length_tested": N,
        "max_horizon_tested": MAX_STEPS,
        "epsilon_standing_hypothesis_check": {
            "violations": eps_hypothesis_violations,
            "holds": eps_hypothesis_holds,
        },
        "value_function_sufficiency": {
            "pairs_checked_across_all_horizons": pairs_checked,
            "violations": violations,
            "policy_errors": policy_errors,
            "sufficiency_holds": sufficiency_holds,
        },
        "all_checks_pass": sufficiency_holds and eps_hypothesis_holds,
    }
}

raw = json.dumps(receipt, indent=2, sort_keys=True)
receipt["receipt_sha256_without_hash_field"] = hashlib.sha256(raw.encode()).hexdigest()
OUT.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")

print("epsilon_standing_hypothesis_holds:", eps_hypothesis_holds)
print("pairs_checked_across_all_horizons:", pairs_checked)
print("policy_errors:", len(policy_errors))
print("violations:", len(violations))
print("sufficiency_holds:", sufficiency_holds)
print("all_checks_pass:", receipt["receipt_H_value_function_sufficiency_T18"]["all_checks_pass"])
print("sha256:", receipt["receipt_sha256_without_hash_field"])
