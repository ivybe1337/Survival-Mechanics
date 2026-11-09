"""Receipt I generator for T19 (nondeterministic non-canonicity: T16's
canonical-presentation-uniqueness theorem does NOT extend to a nondeterministic
generalization of the exact-reachable-presentation category, even holding the
state count fixed at the deterministic optimum |kappa-classes|).

Survival rule: the paper's own running "avoid bb" example (Sigma={a,b},
H=Sigma*, survives(w) iff 'bb' never occurs in w). Deterministic minimum is
3 states (classes A, B, D per T3/T14/T16's existing 3-state shortcut).

Formalization (see paper Definition block for full prose):
  A nondeterministic presentation is (S, delta, lam, s0) with
  delta: S x Sigma -> nonempty subset of S (total), lam: S -> {0,1}, s0 in S.
  Reach(h) subset of S: Reach("") = {s0}; Reach(h.e) = union_{s in Reach(h)}
  delta(s,e). safe(M) := AND_{s in M} lam(s).
  EXACT: for every w in Sigma*, safe(Reach(w)) == survives(w).
  REACHABLE (as a presentation): every state in S occurs in Reach(w) for some w.
  ISOMORPHIC: a bijection psi:S1->S2 with psi(s0_1)=s0_2, lam2(psi(s))=lam1(s)
  for all s, and psi[delta1(s,e)] == delta2(psi(s),e) (image of the SET) for
  all s,e.

This script:
  1. Defines the canonical presentation P_kappa (the deterministic 3-state
     automaton, viewed degenerately as a nondeterministic one with singleton
     delta) and an explicit alternate presentation P_alt (found by exhaustive
     search, hand-verified in the paper's proof) at the SAME state count m=3.
  2. Independently verifies, from raw definitions (no shortcuts), that BOTH
     are exact (via an unbounded, exact product-equivalence decision
     procedure against the canonical target DFA -- not a bounded/truncated
     check) and reachable.
  3. Independently verifies P_alt is NOT isomorphic to P_kappa (exhaustive
     check over all 2 forced-start-preserving bijections of the non-start
     states; also gives the cardinality-mismatch short argument).
  4. Re-runs the FULL exhaustive search over all labeled 3-state
     presentations (identical in spirit to the exploratory search, rewritten
     standalone here) and reports: total valid (exact+reachable) 3-state
     presentations, and the number of pairwise-non-isomorphic classes among
     them -- confirming P_kappa and P_alt sit in two of (at least) 164
     distinct isomorphism classes, i.e. genuine, exhaustively-confirmed
     non-uniqueness, not an isolated fluke.

Integer/boolean arithmetic only. No floats, no randomness, fully
deterministic and independently re-executable.
"""
from __future__ import annotations
import json, hashlib
from pathlib import Path
from itertools import product, permutations

OUT = Path(__file__).with_name("nfa_noncanonicity_receipt.json")
ALPHA = ("a", "b")


def survives(w: str) -> bool:
    return "bb" not in w


# ---------------------------------------------------------------------
# Target canonical DFA for "avoid bb" (ground truth, independent of the
# nondeterministic presentations under test).
# ---------------------------------------------------------------------
TARGET = {
    "states": ["A", "B", "D"],
    "start": "A",
    "trans": {
        ("A", "a"): "A", ("A", "b"): "B",
        ("B", "a"): "A", ("B", "b"): "D",
        ("D", "a"): "D", ("D", "b"): "D",
    },
    "accept": {"A", "B"},
}


def words_upto(alpha, max_len):
    yield ""
    for n in range(1, max_len + 1):
        for tup in product(alpha, repeat=n):
            yield "".join(tup)


TARGET_CROSSCHECK_MAX_LEN = 16


def crosscheck_target_against_survives():
    """Independently confirm TARGET (the hardcoded 3-state DFA dict used as
    ground truth throughout this script) actually computes survives(w), so
    that the exactness checks, which compare candidates against TARGET, rest
    on a verified encoding of the raw rule. Walks TARGET's own transition
    function directly (not via any candidate presentation's machinery) for
    every string up to length TARGET_CROSSCHECK_MAX_LEN and compares final-
    state acceptance against survives(w)."""
    mismatches = []
    checked = 0
    for w in words_upto(ALPHA, TARGET_CROSSCHECK_MAX_LEN):
        s = TARGET["start"]
        for ch in w:
            s = TARGET["trans"][(s, ch)]
        target_says = s in TARGET["accept"]
        checked += 1
        if target_says != survives(w):
            mismatches.append(w)
    return checked, mismatches


def popcount_bits(mask, m):
    return [s for s in range(m) if (mask >> s) & 1]


def build_step(delta, m):
    def step(mask, e):
        r = 0
        mm = mask
        s = 0
        while mm:
            if mm & 1:
                r |= delta[(s, e)]
            mm >>= 1
            s += 1
        return r
    return step


def safe_mask(mask, lam, m):
    mm = mask
    s = 0
    while mm:
        if mm & 1 and lam[s] == 0:
            return False
        mm >>= 1
        s += 1
    return True


def states_reachable(delta, m):
    step = build_step(delta, m)
    seen = {1}
    frontier = [1]
    union_mask = 1
    while frontier:
        nxt = []
        for mask in frontier:
            for e in ALPHA:
                nm = step(mask, e)
                union_mask |= nm
                if nm not in seen:
                    seen.add(nm)
                    nxt.append(nm)
        frontier = nxt
    return set(popcount_bits(union_mask, m)), seen


def check_exact_unbounded(delta, lam, m, target):
    """Exact (unbounded, not horizon-truncated) equivalence check between the
    mask-automaton (accept = safe(mask)) and the target DFA, via product BFS
    over reachable product states -- a genuine decision procedure for regular
    language equivalence, since both automata are finite-state."""
    step = build_step(delta, m)
    start_pair = (1, target["start"])
    seen = {start_pair}
    frontier = [start_pair]
    while frontier:
        nxt = []
        for (mask, ts) in frontier:
            if safe_mask(mask, lam, m) != (ts in target["accept"]):
                return False
            for e in ALPHA:
                nmask = step(mask, e)
                nts = target["trans"][(ts, e)]
                np = (nmask, nts)
                if np not in seen:
                    seen.add(np)
                    nxt.append(np)
        frontier = nxt
    return True


def is_isomorphic(delta_a, lam_a, delta_b, lam_b, m):
    others = list(range(1, m))
    for perm in permutations(others):
        psi = [0] * m
        for i, o in enumerate(others):
            psi[o] = perm[i]
        if any(lam_b[psi[s]] != lam_a[s] for s in range(m)):
            continue
        ok = True
        for s in range(m):
            for e in ALPHA:
                mask_a = delta_a[(s, e)]
                img = 0
                mm, ss = mask_a, 0
                while mm:
                    if mm & 1:
                        img |= (1 << psi[ss])
                    mm >>= 1
                    ss += 1
                if img != delta_b[(psi[s], e)]:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True
    return False


# ---------------------------------------------------------------------
# P_kappa: canonical presentation (states 0=A,1=B,2=D), singleton delta.
# ---------------------------------------------------------------------
DELTA_KAPPA = {
    (0, "a"): 0b001, (0, "b"): 0b010,   # A --a--> A ; A --b--> B
    (1, "a"): 0b001, (1, "b"): 0b100,   # B --a--> A ; B --b--> D
    (2, "a"): 0b100, (2, "b"): 0b100,   # D --a--> D ; D --b--> D
}
LAM_KAPPA = (1, 1, 0)

# ---------------------------------------------------------------------
# P_alt: the alternate presentation found by exhaustive search. State 0 is
# still the start; state 0's own 'b'-transition is nondeterministic, landing
# in BOTH state 0 and state 1 simultaneously ({0,1}), so a single raw state
# no longer corresponds 1:1 with a kappa-class -- a genuinely different
# (non-"padding") structural encoding of the same exact behaviour.
# ---------------------------------------------------------------------
DELTA_ALT = {
    (0, "a"): 0b001, (0, "b"): 0b011,   # 0 --a--> {0} ; 0 --b--> {0,1}
    (1, "a"): 0b001, (1, "b"): 0b100,   # 1 --a--> {0} ; 1 --b--> {2}
    (2, "a"): 0b100, (2, "b"): 0b100,   # 2 --a--> {2} ; 2 --b--> {2}
}
LAM_ALT = (1, 1, 0)

M = 3


def subsets_nonempty(m):
    return list(range(1, (1 << m)))


def full_search(m, target):
    subs = subsets_nonempty(m)
    entries = [(s, e) for s in range(m) for e in ALPHA]
    n_entries = len(entries)
    lam0 = 1 if target["start"] in target["accept"] else 0
    other_lam_bits = list(product([0, 1], repeat=m - 1))
    valid = []
    for delta_tuple in product(subs, repeat=n_entries):
        delta = {entries[i]: delta_tuple[i] for i in range(n_entries)}
        reach_states, _ = states_reachable(delta, m)
        if reach_states != set(range(m)):
            continue
        for lam_rest in other_lam_bits:
            lam = tuple([lam0] + list(lam_rest))
            if check_exact_unbounded(delta, lam, m, target):
                valid.append((delta, lam))
    return valid


def group_classes(valid, m):
    classes = []
    for cand in valid:
        d, l = cand
        placed = False
        for cls in classes:
            d0, l0 = cls[0]
            if is_isomorphic(d, l, d0, l0, m):
                cls.append(cand)
                placed = True
                break
        if not placed:
            classes.append([cand])
    return classes


def main():
    # --- Part 0: TARGET itself is a correct encoding of survives(), checked
    # independently rather than trusted, since everything else in this
    # script checks candidates against TARGET. ---
    target_checked, target_mismatches = crosscheck_target_against_survives()
    target_matches_survives = len(target_mismatches) == 0

    # --- Part 1: the two named witnesses, checked from raw definitions ---
    p_kappa_reach_states, _ = states_reachable(DELTA_KAPPA, M)
    p_kappa_reachable_ok = (p_kappa_reach_states == set(range(M)))
    p_kappa_exact = check_exact_unbounded(DELTA_KAPPA, LAM_KAPPA, M, TARGET)

    p_alt_reach_states, _ = states_reachable(DELTA_ALT, M)
    p_alt_reachable_ok = (p_alt_reach_states == set(range(M)))
    p_alt_exact = check_exact_unbounded(DELTA_ALT, LAM_ALT, M, TARGET)

    witnesses_non_isomorphic = not is_isomorphic(DELTA_KAPPA, LAM_KAPPA, DELTA_ALT, LAM_ALT, M)
    cardinality_mismatch_argument = (
        bin(DELTA_ALT[(0, "b")]).count("1") != bin(DELTA_KAPPA[(0, "b")]).count("1")
    )

    # sanity: also confirm P_alt is genuinely nondeterministic (not secretly
    # reducible to a singleton-delta / deterministic presentation).
    p_alt_is_genuinely_nondeterministic = any(
        bin(DELTA_ALT[(s, e)]).count("1") > 1 for s in range(M) for e in ALPHA
    )
    # confirm the multi-element target set {0,1} reached via (0,'b') is
    # itself a LIVE mask (all lam=1), i.e. not reducible to "dead padding".
    live_multistate_mask_used = (
        DELTA_ALT[(0, "b")] == 0b011 and safe_mask(0b011, LAM_ALT, M)
    )

    # --- Part 2: full exhaustive re-search at m=3, isomorphism classes ---
    valid = full_search(M, TARGET)
    classes = group_classes(valid, M)

    # confirm P_kappa and P_alt each land in the search results, in
    # DIFFERENT classes, as an additional cross-check on the isomorphism
    # tester itself.
    p_kappa_in_search = any(d == DELTA_KAPPA and l == LAM_KAPPA for d, l in valid)
    p_alt_in_search = any(d == DELTA_ALT and l == LAM_ALT for d, l in valid)

    def class_index_of(delta, lam):
        for i, cls in enumerate(classes):
            d0, l0 = cls[0]
            if is_isomorphic(delta, lam, d0, l0, M):
                return i
        return None

    p_kappa_class = class_index_of(DELTA_KAPPA, LAM_KAPPA)
    p_alt_class = class_index_of(DELTA_ALT, LAM_ALT)
    witnesses_in_distinct_classes_per_full_search = (
        p_kappa_class is not None and p_alt_class is not None and p_kappa_class != p_alt_class
    )

    def delta_repr(delta, m):
        return {f"({s},{e})": popcount_bits(delta[(s, e)], m) for s in range(m) for e in ALPHA}

    receipt = {
        "receipt_I_nfa_noncanonicity_T19": {
            "alphabet": ALPHA,
            "survival_rule": "trace survives iff substring 'bb' never occurs",
            "state_count_m": M,
            "deterministic_minimum_state_count": 3,
            "target_dfa_crosscheck_against_raw_survives": {
                "strings_checked": target_checked,
                "max_length_checked": TARGET_CROSSCHECK_MAX_LEN,
                "mismatches": target_mismatches,
                "target_matches_survives": target_matches_survives,
            },
            "witness_P_kappa": {
                "delta": delta_repr(DELTA_KAPPA, M),
                "lam": LAM_KAPPA,
                "reachable": p_kappa_reachable_ok,
                "exact": p_kappa_exact,
            },
            "witness_P_alt": {
                "delta": delta_repr(DELTA_ALT, M),
                "lam": LAM_ALT,
                "reachable": p_alt_reachable_ok,
                "exact": p_alt_exact,
                "genuinely_nondeterministic": p_alt_is_genuinely_nondeterministic,
                "uses_a_live_multistate_reachable_mask": live_multistate_mask_used,
            },
            "witnesses_non_isomorphic": witnesses_non_isomorphic,
            "cardinality_mismatch_short_argument_holds": cardinality_mismatch_argument,
            "full_exhaustive_search_m3": {
                "total_valid_exact_reachable_presentations": len(valid),
                "isomorphism_class_count": len(classes),
                "class_sizes": sorted([len(c) for c in classes]),
                "p_kappa_found_in_search": p_kappa_in_search,
                "p_alt_found_in_search": p_alt_in_search,
                "witnesses_in_distinct_classes_per_full_search": witnesses_in_distinct_classes_per_full_search,
            },
            "all_checks_pass": (
                target_matches_survives and
                p_kappa_reachable_ok and p_kappa_exact and
                p_alt_reachable_ok and p_alt_exact and
                witnesses_non_isomorphic and cardinality_mismatch_argument and
                p_alt_is_genuinely_nondeterministic and live_multistate_mask_used and
                p_kappa_in_search and p_alt_in_search and
                witnesses_in_distinct_classes_per_full_search and
                len(classes) >= 2
            ),
        }
    }

    raw = json.dumps(receipt, indent=2, sort_keys=True)
    receipt["receipt_sha256_without_hash_field"] = hashlib.sha256(raw.encode()).hexdigest()
    OUT.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")

    r = receipt["receipt_I_nfa_noncanonicity_T19"]
    print("TARGET matches raw survives() over", target_checked, "strings:", target_matches_survives)
    print("P_kappa reachable/exact:", r["witness_P_kappa"]["reachable"], r["witness_P_kappa"]["exact"])
    print("P_alt reachable/exact:", r["witness_P_alt"]["reachable"], r["witness_P_alt"]["exact"])
    print("P_alt genuinely nondeterministic:", r["witness_P_alt"]["genuinely_nondeterministic"])
    print("P_alt uses live multistate mask:", r["witness_P_alt"]["uses_a_live_multistate_reachable_mask"])
    print("witnesses non-isomorphic:", r["witnesses_non_isomorphic"])
    print("cardinality mismatch argument holds:", r["cardinality_mismatch_short_argument_holds"])
    print("full search: valid =", r["full_exhaustive_search_m3"]["total_valid_exact_reachable_presentations"],
          "iso classes =", r["full_exhaustive_search_m3"]["isomorphism_class_count"])
    print("witnesses land in distinct classes per full search:",
          r["full_exhaustive_search_m3"]["witnesses_in_distinct_classes_per_full_search"])
    print("all_checks_pass:", r["all_checks_pass"])
    print("sha256:", receipt["receipt_sha256_without_hash_field"])


if __name__ == "__main__":
    main()
