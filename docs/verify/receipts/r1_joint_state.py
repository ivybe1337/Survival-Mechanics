"""
Receipt R1 -- predictive state, residual state, joint state.

Checks (exact arithmetic throughout):
  1. The predictive-state congruence (causal-state equivalence with a single null class)
     is a right congruence, exhaustively on several processes, including one with
     zero-probability histories.
  2. For the phase-biased Bernoulli process, epsilon(h) = |h| mod k exactly (k = 2, 3).
  3. Residual state of "avoid bb" has exactly 3 classes, computed two independent ways
     (DFA minimization, and raw residual rows).
  4. Independence theorem witness: under the parity process and "avoid bb", neither
     partition refines the other and the joint partition has 2 * 3 = 6 classes.
  5. Index sandwich max(|eps|,|kappa|) <= |J| <= |eps||kappa|, with the equality
     characterization, on several (process, rule) pairs.
"""
from fractions import Fraction as F

from la_core import (AVOID_BB, DFA, HMM, Checks, dfa_avoid, iid, parity_bernoulli, partition,
                      phase_bernoulli, refines, residual_row, words, write_receipt)

ALPH = ("a", "b")
C = Checks()
out = {}

H_LEN = 9          # histories up to this length
SUF_LEN = 6        # residual rows over suffixes up to this length

hist = words(ALPH, H_LEN)

# ---------------------------------------------------------------- processes
golden_mean = HMM(ALPH, [1, 0], {  # never emits "bb": state 0 = last not b, state 1 = last b
    "a": [[F(1, 3), 0], [1, 0]],
    "b": [[0, F(2, 3)], [0, 0]],
})
order1 = HMM(ALPH, [F(1, 2), F(1, 2), 0], {  # state 2 unused initially; a 3-state order-1 chain
    "a": [[F(1, 5), 0, 0], [0, 0, F(1, 2)], [F(3, 4), 0, 0]],
    "b": [[0, F(4, 5), 0], [0, 0, F(1, 2)], [0, F(1, 4), 0]],
})
processes = {
    "parity_9_10": parity_bernoulli(F(9, 10), F(1, 10)),
    "phase3": phase_bernoulli([F(1, 2), F(1, 3), F(1, 5)]),
    "iid_1_3": iid(F(1, 3)),
    "golden_mean_no_bb": golden_mean,
    "order1_mix": order1,
}


def eps_key(P):
    cache = {}

    def k(h):
        if h not in cache:
            cache[h] = P.eps_signature(h)
        return cache[h]
    return k


# ---------------------------------------------------------------- 1. right congruence of epsilon
rc_report = {}
for name, P in processes.items():
    k = eps_key(P)
    hs = words(ALPH, 7)
    blocks = partition(hs, lambda h: k(h))
    viol = 0
    checks = 0
    for b in blocks:
        rep = b[0]
        for h in b[1:]:
            for e in ALPH:
                checks += 1
                if k(rep + e) != k(h + e):
                    viol += 1
    null_count = sum(1 for h in hs if k(h) is None)
    rc_report[name] = {"histories": len(hs), "classes": len(blocks), "null_histories": null_count,
                       "extension_checks": checks, "violations": viol}
    C.check(f"eps_right_congruence[{name}]", viol == 0, rc_report[name])
C.check("some_process_has_null_histories", rc_report["golden_mean_no_bb"]["null_histories"] > 0,
        rc_report["golden_mean_no_bb"]["null_histories"])
out["epsilon_right_congruence"] = rc_report

# ---------------------------------------------------------------- 2. epsilon = |h| mod k for phase processes
for name, k_ in (("parity_9_10", 2), ("phase3", 3)):
    k = eps_key(processes[name])
    blocks = partition(hist, lambda h: k(h))
    by_len = partition(hist, lambda h: len(h) % k_)
    C.check(f"eps_equals_length_mod_{k_}[{name}]", blocks == by_len,
            {"eps_classes": len(blocks), "length_mod_classes": len(by_len)})

# ---------------------------------------------------------------- 3. kappa for avoid bb, two ways
V = AVOID_BB.V
suffixes = words(ALPH, SUF_LEN)
kappa_rows = partition(hist, lambda h: residual_row(V, h, suffixes))
kappa_dfa = partition(hist, AVOID_BB.kappa)
C.check("kappa_avoid_bb_three_classes", len(kappa_rows) == 3 and kappa_rows == kappa_dfa,
        {"rows": len(kappa_rows), "dfa": len(kappa_dfa)})

# ---------------------------------------------------------------- 4. independence witness
Pp = processes["parity_9_10"]
ke = eps_key(Pp)
eps_part = partition(hist, ke)
kap_part = kappa_dfa
J_part = partition(hist, lambda h: (ke(h), AVOID_BB.kappa(h)))
C.check("witness_same_kappa_diff_eps", AVOID_BB.kappa("") == AVOID_BB.kappa("a") and ke("") != ke("a"))
C.check("witness_same_eps_diff_kappa", ke("a") == ke("b") and AVOID_BB.kappa("a") != AVOID_BB.kappa("b"))
C.check("eps_does_not_refine_kappa", not refines(eps_part, kap_part))
C.check("kappa_does_not_refine_eps", not refines(kap_part, eps_part))
C.check("joint_has_product_index_6", len(J_part) == 6 == len(eps_part) * len(kap_part),
        {"eps": len(eps_part), "kappa": len(kap_part), "J": len(J_part)})
reps = {}
for h in ["", "a", "b", "ab", "bb", "abb"]:
    reps[h] = [str(ke(h)[0]) if ke(h) else None, AVOID_BB.kappa(h)]
C.check("six_named_representatives_pairwise_distinct",
        len({(ke(h), AVOID_BB.kappa(h)) for h in reps}) == 6, reps)
out["independence_witness"] = {"eps_classes": len(eps_part), "kappa_classes": len(kap_part),
                               "J_classes": len(J_part), "representatives": reps}

# ---------------------------------------------------------------- 5. index sandwich + equality characterization
parity_len = DFA(ALPH, [0, 1], 0, {(0, "a"): 1, (0, "b"): 1, (1, "a"): 0, (1, "b"): 0}, accept={0})
everything = DFA(ALPH, [0], 0, {(0, "a"): 0, (0, "b"): 0}, accept={0})
rules = {"avoid_bb": AVOID_BB, "avoid_aa": dfa_avoid("aa"), "even_length_alive": parity_len,
         "always_alive": everything, "avoid_aba": dfa_avoid("aba")}
sandwich = {}
hs = words(ALPH, 8)
for pn, P in processes.items():
    k = eps_key(P)
    for rn, D in rules.items():
        E = partition(hs, k)
        K = partition(hs, D.kappa)
        J = partition(hs, lambda h: (k(h), D.kappa(h)))
        lower = max(len(E), len(K)) <= len(J)
        upper = len(J) <= len(E) * len(K)
        comparable = refines(K, E) or refines(E, K)
        eq_char = (len(J) == max(len(E), len(K))) == comparable
        sandwich[f"{pn}|{rn}"] = {"eps": len(E), "kappa": len(K), "J": len(J), "comparable": comparable}
        C.check(f"sandwich[{pn}|{rn}]", lower and upper and eq_char, sandwich[f"{pn}|{rn}"])
C.check("sandwich_has_comparable_case", any(v["comparable"] for v in sandwich.values()))
C.check("sandwich_has_incomparable_case", any(not v["comparable"] for v in sandwich.values()))
out["index_sandwich"] = sandwich

out["checks"] = C.results
out["all_checks_pass"] = C.all_pass()
d = write_receipt("r1_joint_state.json", out)
print("R1 all_checks_pass =", C.all_pass(), "digest", d)
