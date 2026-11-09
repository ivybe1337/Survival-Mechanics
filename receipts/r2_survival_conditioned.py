"""
Receipt R2 -- survival-conditioned prediction.

Setting: process P (exact HMM), monotone admissibility rule V (DFA whose dead states are absorbing).
  S_n(h)   = P(the next n symbols keep h alive | h)          (S_0(h) = V(h))
  Q_n(.|h) = law of the next n symbols given that they keep h alive   (defined when S_n(h) > 0)
  sigma(h) = (future law of h, S_0..S_N, Q_1..Q_N)            -- the survival-aware predictive state

Checks:
  1. Sufficiency: S_n and Q_n are constant on joint classes J = (eps, kappa)   [all h up to length 8, n <= 6]
  2. Exactness:   with full support and monotone V, the partition induced by sigma equals the J partition.
  3. Necessity:   eps alone and kappa alone are each insufficient (explicit witnesses).
  4. Quantitative separation: kappa-blind and eps-blind forecasts can be forced to total-variation
     error arbitrarily close to 1/2 (the gap between the two conditioned laws tends to 1).
  5. Monotonicity S_{n+1} <= S_n.
  6. Infinite horizon: the regime-mixture example, closed forms for S_n, S_infinity and the
     conditioned (Doob-transformed) forecast, checked exactly.
"""
from fractions import Fraction as F

from la_core import (AVOID_BB, DFA, HMM, Checks, dfa_avoid, iid, parity_bernoulli, partition, words,
                      write_receipt)

ALPH = ("a", "b")
C = Checks()
out = {}


def S_Q(P, D, h, n):
    """Exact S_n(h) and Q_n(.|h) (dict over Sigma^n) for monotone DFA semantics D."""
    if P.p(h) == 0:
        return None
    if D.V(h) == 0:
        return (F(0), None)
    tot = F(0)
    mass = {}
    for z in words(ALPH, n, n):
        if D.V(h + z) == 1:  # monotone: V(hz)=1 iff every prefix alive
            pz = P.P_h(h, z)
            if pz > 0:          # a law is a function on outcomes; zero-mass atoms are not recorded
                mass[z] = pz
            tot += pz
    if tot == 0:
        return (F(0), None)
    return (tot, tuple(sorted((z, m / tot) for z, m in mass.items())))


def monotone_ok(D, max_len=8):
    for w in words(ALPH, max_len):
        if D.V(w) == 0 and any(D.V(w + e) == 1 for e in ALPH):
            return False
    return True


def tv(q1, q2):
    d1, d2 = dict(q1), dict(q2)
    keys = set(d1) | set(d2)
    return sum(abs(d1.get(k, F(0)) - d2.get(k, F(0))) for k in keys) / 2


# ---------------------------------------------------------------- examples
parity = parity_bernoulli(F(9, 10), F(1, 10))
three_state = HMM(ALPH, [F(1, 2), F(1, 3), F(1, 6)], {  # full-support, 3-state, non-unifilar
    "a": [[F(1, 4), F(1, 8), F(1, 8)], [F(1, 6), F(1, 3), F(1, 6)], [F(1, 20), F(1, 10), F(1, 10)]],
    "b": [[F(1, 4), F(1, 8), F(1, 8)], [F(1, 6), 0, F(1, 6)], [F(1, 5), F(1, 5), F(7, 20)]],
})
avoid_aab = dfa_avoid("aab")
cases = {"parity_9_10|avoid_bb": (parity, AVOID_BB), "three_state|avoid_aab": (three_state, avoid_aab),
         "parity_9_10|avoid_aab": (parity, avoid_aab)}

HL, NMAX = 8, 6
for name, (P, D) in cases.items():
    C.check(f"monotone_semantics[{name}]", monotone_ok(D))
    hs = words(ALPH, HL)
    C.check(f"full_support[{name}]", all(P.p(h) > 0 for h in words(ALPH, 6)))
    ek = {h: P.eps_signature(h) for h in hs}
    J = {h: (ek[h], D.kappa(h)) for h in hs}
    J_blocks = partition(hs, lambda h: J[h])
    # 1. sufficiency
    viol = 0
    sig = {h: [] for h in hs}
    for n in range(0, NMAX + 1):
        vals = {h: S_Q(P, D, h, n) for h in hs}
        for b in J_blocks:
            if len({vals[h] for h in b}) != 1:
                viol += 1
        for h in hs:
            sig[h].append(vals[h])
    mono = all(sig[h][n + 1][0] <= sig[h][n][0] for h in hs for n in range(NMAX))
    C.check(f"S_monotone[{name}]", mono)
    C.check(f"conditioned_law_factors_through_J[{name}]", viol == 0, {"J_classes": len(J_blocks)})
    # 2. exactness: sigma partition == J partition (horizon 4 is enough here; checked, not assumed)
    sigma_blocks = partition(hs, lambda h: (ek[h], tuple(sig[h][:5])))
    C.check(f"sigma_partition_equals_J[{name}]", sigma_blocks == J_blocks,
            {"sigma": len(sigma_blocks), "J": len(J_blocks)})
    out[name] = {"J_classes_observed": len(J_blocks), "sigma_classes_observed": len(sigma_blocks)}

# ---------------------------------------------------------------- 3. necessity witnesses (parity | avoid bb)
q = lambda h, n=1: S_Q(parity, AVOID_BB, h, n)
C.check("eps_insufficient: eps(a)=eps(b) but Q_1 differ",
        parity.eps_signature("a") == parity.eps_signature("b") and q("a") != q("b"),
        {"Q1(a)": q("a"), "Q1(b)": q("b")})
C.check("kappa_insufficient: kappa('')=kappa(a) but Q_1 differ",
        AVOID_BB.kappa("") == AVOID_BB.kappa("a") and q("") != q("a"),
        {"Q1()": q(""), "Q1(a)": q("a")})

# ---------------------------------------------------------------- 4. quantitative separation
sep = {}
for rho in (F(1, 10), F(1, 100), F(1, 1000)):
    P = iid(rho)
    Sa, Qa = S_Q(P, AVOID_BB, "a", 1)
    Sb, Qb = S_Q(P, AVOID_BB, "b", 1)
    same_eps = P.eps_signature("a") == P.eps_signature("b")
    gap = tv(Qa, Qb)
    sep[f"eps_blind_rho={rho}"] = {"TV": gap, "S1(a)": Sa, "S1(b)": Sb}
    C.check(f"eps_blind_gap[rho={rho}]", same_eps and gap == 1 - rho and Sa == 1 and Sb == rho)
for delta in (F(1, 10), F(1, 100), F(1, 1000)):
    P = parity_bernoulli(1 - delta, delta)
    S0, Q0 = S_Q(P, AVOID_BB, "", 1)
    S1, Q1 = S_Q(P, AVOID_BB, "a", 1)
    gap = tv(Q0, Q1)
    sep[f"kappa_blind_delta={delta}"] = {"TV": gap}
    C.check(f"kappa_blind_gap[delta={delta}]",
            AVOID_BB.kappa("") == AVOID_BB.kappa("a") and gap == 1 - 2 * delta)
out["separation"] = sep

# ---------------------------------------------------------------- 6. infinite horizon: regime mixture
regime = HMM(ALPH, [F(1, 2), F(1, 2)], {"a": [[1, 0], [0, F(1, 2)]], "b": [[0, 0], [0, F(1, 2)]]})
fib = [0, 1, 1]
while len(fib) < 40:
    fib.append(fib[-1] + fib[-2])
inf_ok = True
detail = {}
for k in range(0, 5):
    h = "a" * k
    wA = F(1, 1) / (1 + F(1, 2 ** k))            # posterior weight of the safe regime after a^k
    for n in range(0, 15):
        S = S_Q(regime, AVOID_BB, h, n)[0]
        # bb-free continuations of a^k of length n: words of length n avoiding bb (k>=1 or k=0 same)
        closed = wA + (1 - wA) * F(fib[n + 2], 2 ** n)
        if S != closed:
            inf_ok = False
    detail[f"S_inf(a^{k})"] = wA
C.check("regime_S_n_closed_form", inf_ok)
# S_inf(h) = P(safe regime | h) * 1[h alive]; histories containing b have S_inf = 0.
# Conditioned-forever forecast at the root: Q_inf(e) = P(e) S_inf(e) / S_inf("")
Pa = regime.P_h("", "a")
Pb = regime.P_h("", "b")
S_inf_root = F(1, 2)
S_inf_a = F(1) / (1 + F(1, 2))
S_inf_b = F(0)
Qa_inf = Pa * S_inf_a / S_inf_root
Qb_inf = Pb * S_inf_b / S_inf_root
C.check("regime_doob_forecast_collapses_to_a", Qa_inf == 1 and Qb_inf == 0,
        {"P(a)": Pa, "P(b)": Pb, "Q_inf(a)": Qa_inf, "Q_inf(b)": Qb_inf})
# the unconditioned forecast is 3/4 : 1/4 -- conditioning on survival changes it maximally
C.check("regime_unconditioned_forecast", Pa == F(3, 4) and Pb == F(1, 4))
out["infinite_horizon_regime"] = detail

# ---------------------------------------------------------------- 7. Yaglom (quasi-stationary) forecast when S_inf = 0
fair = iid(F(1, 2))
yag = True
for n in range(1, 25):
    S, Q = S_Q(fair, AVOID_BB, "", n)
    first_a = sum(m for z, m in Q if z[0] == "a")
    if S != F(fib[n + 2], 2 ** n) or first_a != F(fib[n + 1], fib[n + 2]):
        yag = False
    Sb, Qb = S_Q(fair, AVOID_BB, "b", n)
    if sum(m for z, m in Qb if z[0] == "a") != 1:
        yag = False
C.check("yaglom_first_symbol_law_F(n+1)/F(n+2)", yag)
# consecutive Fibonacci ratios converge to 1/phi; check the sandwich |F(n+1)/F(n+2) - 1/phi| < 1/F(n+2)^2 exactly
# via the integer Cassini identity F(n+1)^2 - F(n)F(n+2) = (-1)^n
C.check("cassini_identity_n<=35", all(fib[n + 1] ** 2 - fib[n] * fib[n + 2] == (-1) ** n for n in range(1, 36)))

# ---------------------------------------------------------------- 8. finite-horizon exactness
# J is determined by sigma truncated at horizon max(k-2, m-1), k = ind kappa, m = process dimension.
def trunc_sigma(P, D, h, H):
    law = tuple(P.P_h(h, z) for z in words(ALPH, H)) if P.p(h) > 0 else None
    return (law, tuple(S_Q(P, D, h, n) for n in range(0, H + 1)))

fh = {}
for name, (P, D), m in (("parity_9_10|avoid_bb", cases["parity_9_10|avoid_bb"], 2),
                        ("three_state|avoid_aab", cases["three_state|avoid_aab"], 3),
                        ("parity_9_10|avoid_aab", cases["parity_9_10|avoid_aab"], 2)):
    k = D.index()
    Hstar = max(k - 2, m - 1)
    hs = words(ALPH, 7)
    J_blocks = partition(hs, lambda h: (P.eps_signature(h), D.kappa(h)))
    T_blocks = partition(hs, lambda h: trunc_sigma(P, D, h, Hstar))
    fh[name] = {"kappa_index": k, "process_dim": m, "horizon": Hstar, "J": len(J_blocks), "sigma_trunc": len(T_blocks)}
    C.check(f"finite_horizon_exactness[{name}]", J_blocks == T_blocks, fh[name])
out["finite_horizon_exactness"] = fh

# ---------------------------------------------------------------- 9. full support is necessary for exactness
point = HMM(ALPH, [1], {"a": [[1]], "b": [[0]]})          # emits a forever
Dab = DFA(ALPH, ["s", "a", "ok", "dead"], "s",
          {("s", "a"): "a", ("s", "b"): "ok", ("a", "a"): "ok", ("a", "b"): "dead",
           ("ok", "a"): "ok", ("ok", "b"): "ok", ("dead", "a"): "dead", ("dead", "b"): "dead"},
          accept={"s", "a", "ok"})                            # V(w)=0 iff w starts with ab
sig_eq = all(S_Q(point, Dab, "", n) == S_Q(point, Dab, "a", n) for n in range(0, 7)) and \
    point.eps_signature("") == point.eps_signature("a")
C.check("full_support_needed: sigma(Lambda)=sigma(a) but kappa differs",
        sig_eq and Dab.kappa("") != Dab.kappa("a"))

# ---------------------------------------------------------------- 10. Remark: both ingredients of sigma are needed
markov = HMM(ALPH, [F(1, 2), F(1, 2)], {"a": [[F(3, 10), 0], [F(7, 10), 0]], "b": [[0, F(7, 10)], [0, F(3, 10)]]})
short = DFA(ALPH, [0, 1, 2], 0, {(0, "a"): 1, (0, "b"): 1, (1, "a"): 2, (1, "b"): 2, (2, "a"): 2, (2, "b"): 2},
            accept={0, 1})                                   # V(w)=1 iff |w| <= 1
surv_same = all(S_Q(markov, short, "a", n) == S_Q(markov, short, "b", n) for n in range(0, 6))
C.check("survival_data_alone_do_not_determine_eps",
        surv_same and markov.eps_signature("a") != markov.eps_signature("b"))
horizon_ok = True
for k in range(3, 8):
    states = list(range(k))                                  # 0..k-2 alive lengths, k-1 dead
    d = {(i, e): min(i + 1, k - 1) for i in states for e in ALPH}
    Vk = DFA(ALPH, states, 0, d, accept=set(range(k - 1)))
    fair = iid(F(1, 2))
    horizon_ok &= (Vk.index() == k)
    horizon_ok &= (trunc_sigma(fair, Vk, "", k - 3) == trunc_sigma(fair, Vk, "a", k - 3))
    horizon_ok &= (trunc_sigma(fair, Vk, "", k - 2) != trunc_sigma(fair, Vk, "a", k - 2))
C.check("kappa_part_of_H*_cannot_be_lowered_k=3..7", horizon_ok)

out["checks"] = C.results
out["all_checks_pass"] = C.all_pass()
d = write_receipt("r2_survival_conditioned.json", out)
print("R2 all_checks_pass =", C.all_pass(), "digest", d)
