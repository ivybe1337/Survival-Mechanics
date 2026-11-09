"""
Receipt R6 -- (1) sharpened Lipschitz bound for bounded-horizon feasible sets, (2) the causal-state
machine of the Prop. 8.7 process is infinite while its minimal hidden-state presentations have 2 states.

(1) A^(k)(h) = {e : exists z, |z| <= k-1, V(hez) = 1} (k >= 1), A^(0) = {}.
    Claim: |A^(k)(h) sym A^(k)(h')| <= min(|Sigma|, |(R^(k)(h) sym R^(k)(h')) minus {Lambda}|),
    checked for all ordered pairs of histories of length <= 6, k = 0..4, under a monotone rule (avoid bb)
    and a non-monotone rule (even number of b's), plus both tightness witnesses.
(2) For the process of Prop. 8.7, the predictive states after a^k are pairwise distinct for k <= 40
    (exact rationals), consistent with the proof that there are infinitely many.
"""
from fractions import Fraction as F

from la_core import AVOID_BB, HMM, Checks, words, write_receipt

ALPH = ("a", "b")
C = Checks()
out = {}

V_bb = AVOID_BB.V
V_even = lambda w: 1 if w.count("b") % 2 == 0 else 0


def R(V, h, k):
    return {z for z in words(ALPH, k) if V(h + z) == 1}


def A(V, h, k):
    if k == 0:
        return set()
    return {e for e in ALPH if any(V(h + e + z) == 1 for z in words(ALPH, k - 1))}


hs = words(ALPH, 6)
rep = {}
for name, V in (("avoid_bb", V_bb), ("even_b", V_even)):
    for k in range(0, 5):
        Rk = {h: R(V, h, k) for h in hs}
        Ak = {h: A(V, h, k) for h in hs}
        viol, eq_sharp = 0, 0
        for h in hs:
            for h2 in hs:
                lhs = len(Ak[h] ^ Ak[h2])
                rhs = min(len(ALPH), len((Rk[h] ^ Rk[h2]) - {""}))
                if lhs > rhs:
                    viol += 1
                if lhs == rhs and lhs > 0:
                    eq_sharp += 1
        rep[f"{name},k={k}"] = {"pairs": len(hs) ** 2, "violations": viol, "pairs_with_equality": eq_sharp}
        C.check(f"sharpened_bound[{name},k={k}]", viol == 0, rep[f"{name},k={k}"])
out["sharpened_bound"] = rep
# tightness witnesses
C.check("tight_saturating(h='',h'='bb',k=1..4)",
        all(len(A(V_bb, "", k) ^ A(V_bb, "bb", k)) == 2 for k in range(1, 5)))
C.check("tight_nonsaturating(h='',h'='b',k=1)",
        len(A(V_bb, "", 1) ^ A(V_bb, "b", 1)) == 1 == len((R(V_bb, "", 1) ^ R(V_bb, "b", 1)) - {""}))

# (2) causal states of the Prop 8.7 process
Ta = [[F(1, 2), F(1, 4)], [F(1, 8), F(1, 8)]]
Tb = [[F(1, 8), F(1, 8)], [F(1, 4), F(1, 2)]]
P = HMM(ALPH, [F(1, 2), F(1, 2)], {"a": Ta, "b": Tb})
sigs = [P.eps_signature("a" * k) for k in range(0, 41)]
C.check("predictive_states_after_a^k_pairwise_distinct_k<=40", len(set(sigs)) == len(sigs))
cnt = {L: len({P.eps_signature(h) for h in words(ALPH, L)}) for L in range(0, 9)}
out["distinct_predictive_states_among_histories_up_to_length"] = cnt
C.check("predictive_state_count_grows", all(cnt[L + 1] > cnt[L] for L in range(0, 8)), cnt)

out["checks"] = C.results
out["all_checks_pass"] = C.all_pass()
d = write_receipt("r6_feasible_sets_and_hmm.json", out)
print("R6 all_checks_pass =", C.all_pass(), "digest", d)
