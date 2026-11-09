"""Receipt F generator for T16 (canonical presentation uniqueness / universal
property of the kappa-quotient presentation, resolving U4 within the
discrete deterministic-presentation category this paper works in).
Integer arithmetic only, no floats, no randomness, fully deterministic.

Survival rule reused from Receipt A for continuity: a trace survives iff it
never contains the substring "bb". Alphabet Sigma = {a,b}. H = Sigma* (every
extension is legal, so T11's totalization hypothesis holds trivially: there
is nothing illegal to route to the dead outcome).

This script does three things:
  1. Independently computes kappa(h) for every h up to length N via the same
     raw residual-row method as proof_calculations.py (Receipt A) -- NOT via
     the hand-derived 3-state shortcut description used elsewhere in this
     script -- so the shortcut description used to build P_kappa below is
     itself checked against the ground-truth definition, not merely assumed.
  2. Builds P_kappa (the 3-state minimal presentation: "A" = safe, last
     symbol 'a' or history empty; "B" = safe, last symbol 'b'; "D" = dead,
     already contains "bb") and P_mid (a deliberately non-minimal 4-state
     exact presentation that further splits "A" into "A1" = exactly the
     empty history and "A2" = safe, nonempty, last symbol 'a') and checks
     both are exact presentations per T16's definition, exhaustively over
     all h up to length N and all e in Sigma.
  3. Checks that the map psi: P_mid -> P_kappa forced by T16 (psi(A1)=psi(A2)
     ="A", psi(B)="B", psi(D)="D") is transition- and output-compatible
     (the morphism conditions) at every state/symbol pair, and that this is
     the *only* possible assignment (via psi(phi_mid(h)) = kappa(h) for
     every tested h). It also runs one deliberately WRONG candidate map to
     confirm the check is discriminating, not vacuously satisfied.
"""
from __future__ import annotations
import json, hashlib
from pathlib import Path
from itertools import product

OUT = Path(__file__).with_name("presentation_receipt.json")
ALPHA = ("a", "b")
N = 6          # exhaustively test all histories up to this length
SUFFIX_HORIZON = 8   # suffix truncation for the raw kappa computation (well past stabilization)


def survives(w: str) -> bool:
    return "bb" not in w


def words_upto(alpha, max_len):
    yield ""
    for n in range(1, max_len + 1):
        for tup in product(alpha, repeat=n):
            yield "".join(tup)


# ---------------------------------------------------------------------
# Step 1: raw, ground-truth kappa via residual-row comparison (independent
# of the hand-derived 3-state shortcut used below).
# ---------------------------------------------------------------------
def raw_row(h: str):
    return tuple(int(survives(h + z)) for z in words_upto(ALPHA, SUFFIX_HORIZON))


test_histories = list(words_upto(ALPHA, N))
raw_rows = {h: raw_row(h) for h in test_histories}
distinct_rows = sorted(set(raw_rows.values()))
row_to_label = {}
# Label rows by inspection-free rule: the all-zero row is "D"; among the
# rest, assign "A"/"B" by an arbitrary but fixed order (checked below to
# align with the hand-derived shortcut, not assumed to).
for r in distinct_rows:
    row_to_label[r] = None  # filled after cross-check below

raw_kappa_class_count = len(distinct_rows)


# ---------------------------------------------------------------------
# Hand-derived shortcut classifiers (P_kappa, 3 states; P_mid, 4 states).
# ---------------------------------------------------------------------
def kappa_shortcut(h: str) -> str:
    if not survives(h):
        return "D"
    if h != "" and h[-1] == "b":
        return "B"
    return "A"  # empty, or nonempty ending in 'a'


def phi_mid(h: str) -> str:
    if not survives(h):
        return "D"
    if h == "":
        return "A1"
    if h[-1] == "b":
        return "B"
    return "A2"  # nonempty, ends in 'a'


DELTA_KAPPA = {
    ("D", "a"): "D", ("D", "b"): "D",
    ("A", "a"): "A", ("A", "b"): "B",
    ("B", "a"): "A", ("B", "b"): "D",
}
LAMBDA_KAPPA = {"A": 1, "B": 1, "D": 0}

DELTA_MID = {
    ("D", "a"): "D", ("D", "b"): "D",
    ("A1", "a"): "A2", ("A1", "b"): "B",
    ("A2", "a"): "A2", ("A2", "b"): "B",
    ("B", "a"): "A2", ("B", "b"): "D",
}
LAMBDA_MID = {"A1": 1, "A2": 1, "B": 1, "D": 0}

PSI = {"A1": "A", "A2": "A", "B": "B", "D": "D"}   # the morphism T16 forces
PSI_WRONG = {"A1": "A", "A2": "D", "B": "B", "D": "D"}  # deliberately broken


# ---------------------------------------------------------------------
# Cross-check: does the shortcut kappa_shortcut agree with the raw,
# ground-truth row-based kappa (same partition of test_histories)?
# ---------------------------------------------------------------------
shortcut_partition = {}
for h in test_histories:
    shortcut_partition.setdefault(kappa_shortcut(h), []).append(h)

raw_partition = {}
for h in test_histories:
    raw_partition.setdefault(raw_rows[h], []).append(h)

# Two partitions of the same ground set agree iff they induce the same
# set-of-sets, regardless of labeling.
shortcut_groups = sorted(sorted(v) for v in shortcut_partition.values())
raw_groups = sorted(sorted(v) for v in raw_partition.values())
kappa_shortcut_matches_raw_partition = (shortcut_groups == raw_groups)


# ---------------------------------------------------------------------
# Step 2: exactness checks for P_kappa and P_mid (conditions i+ii of T16's
# definition), exhaustively over all h up to length N-1 (so h+e stays
# within the tested range) and all e in Sigma.
# ---------------------------------------------------------------------
def check_exactness(phi, delta, lam, name):
    violations = []
    checked = 0
    for h in words_upto(ALPHA, N - 1):
        s = phi(h)
        # output compatibility
        checked += 1
        if lam[s] != int(survives(h)):
            violations.append({"type": "output", "h": h, "state": s,
                                "lambda": lam[s], "V(h)": int(survives(h))})
        for e in ALPHA:
            checked += 1
            expected_next_state = phi(h + e)
            actual_next_state = delta[(s, e)]
            if actual_next_state != expected_next_state:
                violations.append({"type": "transition", "h": h, "e": e,
                                    "delta_result": actual_next_state,
                                    "phi(he)": expected_next_state})
    return {"name": name, "checked": checked, "violations": violations,
            "exact": len(violations) == 0}


exactness_kappa = check_exactness(kappa_shortcut, DELTA_KAPPA, LAMBDA_KAPPA, "P_kappa")
exactness_mid = check_exactness(phi_mid, DELTA_MID, LAMBDA_MID, "P_mid")


# ---------------------------------------------------------------------
# Step 3: morphism checks. check_morphism_generic checks a candidate map
# psi : S_src -> S_tgt for transition- and output-compatibility, given the
# source presentation's own (delta_src, lambda_src) and the target
# presentation's (delta_tgt, lambda_tgt). Used for the P_mid -> P_kappa
# direction (step 3) and, later, both directions of P_iso <-> P_kappa
# needed to test Part (b)'s isomorphism claim (step 4).
# ---------------------------------------------------------------------
def check_morphism_generic(psi, delta_src, lambda_src, delta_tgt, lambda_tgt, name):
    transition_violations = []
    output_violations = []
    for s in psi:
        if lambda_tgt[psi[s]] != lambda_src[s]:
            output_violations.append({"state": s, "lambda_tgt_of_psi": lambda_tgt[psi[s]],
                                       "lambda_src": lambda_src[s]})
        for e in ALPHA:
            lhs = psi[delta_src[(s, e)]]
            rhs = delta_tgt[(psi[s], e)]
            if lhs != rhs:
                transition_violations.append({"state": s, "e": e, "psi(delta_src)": lhs,
                                               "delta_tgt(psi)": rhs})
    return {
        "name": name,
        "transition_violations": transition_violations,
        "output_violations": output_violations,
        "is_valid_morphism": len(transition_violations) == 0 and len(output_violations) == 0,
    }


morphism_correct = check_morphism_generic(PSI, DELTA_MID, LAMBDA_MID, DELTA_KAPPA, LAMBDA_KAPPA,
                                           "psi (forced by T16, P_mid -> P_kappa)")
morphism_wrong = check_morphism_generic(PSI_WRONG, DELTA_MID, LAMBDA_MID, DELTA_KAPPA, LAMBDA_KAPPA,
                                         "psi_wrong (deliberately broken, sanity check)")

# Forced-uniqueness check: for every tested history h, psi(phi_mid(h)) must
# equal kappa_shortcut(h) directly (this is what "psi is forced" means --
# there is no freedom once phi_mid's fibers are fixed).
forced_uniqueness_violations = []
for h in test_histories:
    if PSI[phi_mid(h)] != kappa_shortcut(h):
        forced_uniqueness_violations.append(h)
forced_uniqueness_ok = len(forced_uniqueness_violations) == 0

# P_mid is genuinely non-minimal: A1 and A2 are distinct phi_mid-states but
# identical kappa-classes -- confirm this witness of non-minimality exists.
non_minimality_witness = {
    "state_A1_example_history": "",
    "state_A2_example_history": "a",
    "phi_mid_distinguishes_them": phi_mid("") != phi_mid("a"),
    "kappa_identifies_them": kappa_shortcut("") == kappa_shortcut("a"),
    "confirms_P_mid_is_strictly_non_minimal": (phi_mid("") != phi_mid("a")) and (kappa_shortcut("") == kappa_shortcut("a")),
}


# ---------------------------------------------------------------------
# Step 4 (Part (b) test -- distinct from step 3, which only exercises
# Part (a)): build a genuinely MINIMAL exact reachable presentation P_iso,
# whose phi-kernel equals ~kappa exactly (a bijective relabeling of
# P_kappa's own states), and check that the forced morphism psi_iso is a
# bijection AND that its set-theoretic inverse satisfies all three
# conditions of the paper's own morphism definition: the structure-map
# condition psi_iso_inv . kappa = phi_iso (not just transition/output
# compatibility, which is all step 3 ever tests).
# ---------------------------------------------------------------------
RELABEL = {"A": "S1", "B": "S2", "D": "S3"}
UNRELABEL = {v: k for k, v in RELABEL.items()}

def phi_iso(h: str) -> str:
    return RELABEL[kappa_shortcut(h)]

DELTA_ISO = {(RELABEL[s], e): RELABEL[nxt] for (s, e), nxt in DELTA_KAPPA.items()}
LAMBDA_ISO = {RELABEL[s]: v for s, v in LAMBDA_KAPPA.items()}

exactness_iso = check_exactness(phi_iso, DELTA_ISO, LAMBDA_ISO, "P_iso")

# minimality check: phi_iso's kernel must equal ~kappa exactly, i.e.
# phi_iso(h) == phi_iso(h') iff kappa_shortcut(h) == kappa_shortcut(h'),
# checked over all tested histories.
minimality_violations = []
for h in test_histories:
    for hp in test_histories:
        same_phi_iso = (phi_iso(h) == phi_iso(hp))
        same_kappa = (kappa_shortcut(h) == kappa_shortcut(hp))
        if same_phi_iso != same_kappa:
            minimality_violations.append([h, hp])
P_iso_is_minimal = len(minimality_violations) == 0

# The forced morphism psi_iso : P_iso -> P_kappa, psi_iso(phi_iso(h)) := kappa(h).
PSI_ISO = {phi_iso(h): kappa_shortcut(h) for h in test_histories}
assert len(PSI_ISO) == 3, "psi_iso should be defined on exactly the 3 states of P_iso"

morphism_iso = check_morphism_generic(PSI_ISO, DELTA_ISO, LAMBDA_ISO, DELTA_KAPPA, LAMBDA_KAPPA,
                                       "psi_iso (P_iso -> P_kappa)")

# Bijectivity of psi_iso.
psi_iso_is_bijective = (
    len(set(PSI_ISO.keys())) == len(set(PSI_ISO.values())) == 3
)

# The inverse map, and a check of ALL THREE morphism conditions for it,
# including the structure-map condition the hand proof's write-up for
# psi^{-1} does not spell out: psi_iso_inv . kappa = phi_iso.
PSI_ISO_INV = {v: k for k, v in PSI_ISO.items()}
structure_map_violations_inv = []
for h in test_histories:
    lhs = PSI_ISO_INV[kappa_shortcut(h)]
    rhs = phi_iso(h)
    if lhs != rhs:
        structure_map_violations_inv.append(h)
structure_map_ok_inv = len(structure_map_violations_inv) == 0

morphism_iso_inv = check_morphism_generic(PSI_ISO_INV, DELTA_KAPPA, LAMBDA_KAPPA, DELTA_ISO, LAMBDA_ISO,
                                           "psi_iso_inv (P_kappa -> P_iso)")

part_b_isomorphism_check = {
    "P_iso_is_exact": exactness_iso["exact"],
    "P_iso_is_minimal": P_iso_is_minimal,
    "psi_iso_is_valid_morphism": morphism_iso["is_valid_morphism"],
    "psi_iso_is_bijective": psi_iso_is_bijective,
    "psi_iso_inverse_is_valid_morphism": morphism_iso_inv["is_valid_morphism"],
    "psi_iso_inverse_structure_map_condition_ok": structure_map_ok_inv,
    "confirms_part_b_isomorphism": (
        exactness_iso["exact"] and P_iso_is_minimal and morphism_iso["is_valid_morphism"]
        and psi_iso_is_bijective and morphism_iso_inv["is_valid_morphism"] and structure_map_ok_inv
    ),
}

receipt = {
    "receipt_F_presentation_uniqueness_T16": {
        "alphabet": ALPHA,
        "survival_rule": "trace survives iff substring 'bb' never occurs",
        "history_length_tested": N,
        "raw_kappa_class_count_via_residual_rows": raw_kappa_class_count,
        "raw_kappa_row_suffix_horizon": SUFFIX_HORIZON,
        "kappa_shortcut_matches_raw_row_partition": kappa_shortcut_matches_raw_partition,
        "exactness_P_kappa": exactness_kappa,
        "exactness_P_mid": exactness_mid,
        "morphism_check_correct_psi": morphism_correct,
        "morphism_check_wrong_psi_sanity": morphism_wrong,
        "forced_uniqueness_ok": forced_uniqueness_ok,
        "forced_uniqueness_violations": forced_uniqueness_violations,
        "non_minimality_witness": non_minimality_witness,
        "part_b_isomorphism_check": part_b_isomorphism_check,
        "all_checks_pass": (
            kappa_shortcut_matches_raw_partition
            and exactness_kappa["exact"]
            and exactness_mid["exact"]
            and morphism_correct["is_valid_morphism"]
            and (not morphism_wrong["is_valid_morphism"])
            and forced_uniqueness_ok
            and non_minimality_witness["confirms_P_mid_is_strictly_non_minimal"]
            and part_b_isomorphism_check["confirms_part_b_isomorphism"]
        ),
    }
}

raw = json.dumps(receipt, indent=2, sort_keys=True)
receipt["receipt_sha256_without_hash_field"] = hashlib.sha256(raw.encode()).hexdigest()
OUT.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")

print("raw_kappa_class_count_via_residual_rows:", raw_kappa_class_count)
print("kappa_shortcut_matches_raw_row_partition:", kappa_shortcut_matches_raw_partition)
print("exactness_P_kappa:", exactness_kappa["exact"], "checked:", exactness_kappa["checked"])
print("exactness_P_mid:", exactness_mid["exact"], "checked:", exactness_mid["checked"])
print("morphism_correct valid:", morphism_correct["is_valid_morphism"])
print("morphism_wrong valid (should be False):", morphism_wrong["is_valid_morphism"])
print("forced_uniqueness_ok:", forced_uniqueness_ok)
print("non_minimality_witness:", non_minimality_witness["confirms_P_mid_is_strictly_non_minimal"])
print("part_b_isomorphism_check:", part_b_isomorphism_check["confirms_part_b_isomorphism"])
print("  details:", part_b_isomorphism_check)
print("all_checks_pass:", receipt["receipt_F_presentation_uniqueness_T16"]["all_checks_pass"])
print("sha256:", receipt["receipt_sha256_without_hash_field"])
