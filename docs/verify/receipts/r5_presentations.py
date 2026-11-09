"""
Receipt R5 -- presentations beyond the deterministic category (closes the rest of U4).

Universal (AND-safe) nondeterministic presentations Q = (S, s0, delta, lam), delta total into nonempty sets,
safe(M) = AND of lam over M, exact iff safe(Reach(h)) = V(h) for all h.

  1. Fooling-set minimality for "avoid bb": no exact universal presentation with 1 or 2 states exists
     (exhaustive), so the two non-isomorphic 3-state presentations of Theorem [nondet non-canonicity]
     are minimum over ALL nondeterministic presentations, not only over those at the deterministic count.
  2. Exponential succinctness, family L_n = "never a b exactly n-1 steps after an a", n = 2..10:
       - survival-state index is exactly 2^(n-1) + 1 (DFA minimization, cross-checked against the raw rule),
       - the (n+1)-state universal presentation U_n is exact (unbounded product-BFS decision procedure),
       - the (n+1)-element fooling set satisfies the fooling-set conditions,
       - exhaustive search: no 3-state exact universal presentation of L_3 exists (so n+1 is optimal at n=3
         by brute force, independently of the fooling-set argument).
  3. Probabilistic non-canonicity: a one-parameter family of pairwise non-isomorphic 2-state HMMs,
     all generating the same process, whose Hankel rank is 2 (so 2 states is minimum).
"""
from fractions import Fraction as F
from itertools import product

from la_core import AVOID_BB, DFA, HMM, Checks, words, write_receipt

ALPH = ("a", "b")
C = Checks()
out = {}


# ---------------------------------------------------------------- universal presentations
def mask_step(delta, mask, e, m):
    r = 0
    for s in range(m):
        if (mask >> s) & 1:
            r |= delta[(s, e)]
    return r


def safe(mask, lam, m):
    return all(lam[s] == 1 for s in range(m) if (mask >> s) & 1)


def exact_against_dfa(delta, lam, m, D):
    """Unbounded decision: BFS over reachable (mask, dfa-state) pairs, checking output agreement."""
    start = (1, D.start)
    seen = {start}
    frontier = [start]
    while frontier:
        nxt = []
        for (mask, q) in frontier:
            if safe(mask, lam, m) != (q in D.accept):
                return False
            for e in ALPH:
                p = (mask_step(delta, mask, e, m), D.delta[(q, e)])
                if p not in seen:
                    seen.add(p)
                    nxt.append(p)
        frontier = nxt
    return True


def states_used(delta, m):
    seen, frontier, used = {1}, [1], 1
    while frontier:
        nxt = []
        for mask in frontier:
            for e in ALPH:
                n = mask_step(delta, mask, e, m)
                used |= n
                if n not in seen:
                    seen.add(n)
                    nxt.append(n)
        frontier = nxt
    return used == (1 << m) - 1


def exhaustive_exists(m, D):
    subs = range(1, 1 << m)
    entries = [(s, e) for s in range(m) for e in ALPH]
    lam0 = 1 if D.start in D.accept else 0
    count = 0
    for dt in product(subs, repeat=len(entries)):
        delta = dict(zip(entries, dt))
        for rest in product((0, 1), repeat=m - 1):
            lam = (lam0,) + rest
            count += 1
            if exact_against_dfa(delta, lam, m, D):
                return True, count
    return False, count


# 1. minimality for avoid bb
for m in (1, 2):
    ex, cnt = exhaustive_exists(m, AVOID_BB)
    C.check(f"avoid_bb_no_exact_universal_presentation_with_{m}_states", not ex, {"candidates": cnt})
fool_bb = [("", "bb"), ("b", "b"), ("bb", "")]
Vbb = AVOID_BB.V
fs_ok = all(Vbb(x + y) == 0 for x, y in fool_bb) and all(
    Vbb(fool_bb[i][0] + fool_bb[j][1]) == 1 or Vbb(fool_bb[j][0] + fool_bb[i][1]) == 1
    for i in range(3) for j in range(3) if i != j)
C.check("avoid_bb_fooling_set_size_3", fs_ok)


# 2. exponential succinctness family
def V_n(n):
    def V(w):
        for i in range(len(w)):
            j = i + n - 1
            if j < len(w) and w[i] == "a" and w[j] == "b":
                return 0
        return 1
    return V


def dfa_n(n):
    """States: tuple of the last n-1 symbols (None-padded), plus 'D'."""
    k = n - 1
    states = [tuple(t) for t in product((None, "a", "b"), repeat=k)] + ["D"]
    delta = {}
    for s in states:
        for e in ALPH:
            if s == "D":
                delta[(s, e)] = "D"
            elif s[0] == "a" and e == "b":
                delta[(s, e)] = "D"
            else:
                delta[(s, e)] = s[1:] + (e,)
    start = tuple([None] * k)
    return DFA(ALPH, states, start, delta, accept=[s for s in states if s != "D"])


def U_n(n):
    """(n+1)-state universal presentation: 0 waits, 1..n-1 count after a guessed a, n is the death state."""
    delta = {}
    delta[(0, "a")] = (1 << 0) | (1 << 1)
    delta[(0, "b")] = 1 << 0
    for i in range(1, n - 1):
        for e in ALPH:
            delta[(i, e)] = 1 << (i + 1)
    delta[(n - 1, "b")] = 1 << n
    delta[(n - 1, "a")] = 1 << 0
    for e in ALPH:
        delta[(n, e)] = 1 << n
    lam = tuple([1] * n + [0])
    return delta, lam, n + 1


fam = {}
for n in range(2, 11):
    D = dfa_n(n)
    V = V_n(n)
    # DFA faithfully encodes the rule (all words up to length n+6)
    enc_ok = all(D.V(w) == V(w) for w in words(ALPH, min(n + 6, 14)))
    idx = D.index()
    delta, lam, m = U_n(n)
    exact = exact_against_dfa(delta, lam, m, D)
    used = states_used(delta, m)
    fool = [("", "a" + "b" * (n - 1))] + [("a" + "b" * (i - 1), "b" * (n - i)) for i in range(1, n)] + \
           [("a" + "b" * (n - 1), "")]
    f_ok = len(fool) == n + 1 and all(V(x + y) == 0 for x, y in fool) and all(
        V(fool[i][0] + fool[j][1]) == 1 or V(fool[j][0] + fool[i][1]) == 1
        for i in range(n + 1) for j in range(n + 1) if i != j)
    info_lb = next(k for k in range(1, 64) if (1 << k) - 1 >= idx)
    fam[n] = {"kappa_index": idx, "predicted": 2 ** (n - 1) + 1, "universal_states": m,
              "exact": exact, "all_states_used": used, "fooling_set_ok": f_ok, "subset_lower_bound": info_lb}
    C.check(f"succinctness[n={n}]", enc_ok and idx == 2 ** (n - 1) + 1 and exact and used and f_ok
            and info_lb <= m, fam[n])
out["succinctness_family"] = fam

ex3, cnt3 = exhaustive_exists(3, dfa_n(3))
C.check("L_3_no_exact_universal_presentation_with_3_states", not ex3, {"candidates": cnt3})

# 3. probabilistic non-canonicity
Ta = [[F(1, 2), F(1, 4)], [F(1, 8), F(1, 8)]]
Tb = [[F(1, 8), F(1, 8)], [F(1, 4), F(1, 2)]]
pi = [F(1, 2), F(1, 2)]


def mm(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def transformed(t):
    S = [[F(1), F(0)], [t, 1 - t]]
    det = 1 - t
    Si = [[F(1), F(0)], [-t / det, 1 / det]]
    return (mm(mm(Si, Ta), S), mm(mm(Si, Tb), S), [pi[0] + pi[1] * t, pi[1] * (1 - t)])


base = HMM(ALPH, pi, {"a": Ta, "b": Tb})
W = words(ALPH, 3)
hank = [[base.p(u + v) for v in W] for u in W]


def rank(M):
    M = [list(r) for r in M]
    rk = 0
    for c in range(len(M[0])):
        piv = next((r for r in range(rk, len(M)) if M[r][c] != 0), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        for r in range(len(M)):
            if r != rk and M[r][c] != 0:
                f = M[r][c] / M[rk][c]
                M[r] = [M[r][k] - f * M[rk][k] for k in range(len(M[0]))]
        rk += 1
    return rk


C.check("hankel_rank_is_2", rank(hank) == 2)
family = {}
reps = []
for t in (F(-1, 2), F(-1, 4), F(0), F(1, 10), F(1, 5), F(1, 4)):
    A2, B2, p2 = transformed(t)
    h = HMM(ALPH, p2, {"a": A2, "b": B2})  # constructor asserts stochasticity and nonnegativity
    same_law = all(h.p(w) == base.p(w) for w in words(ALPH, 6))  # 2+2-1 = 3 suffices; 6 checked
    reps.append((t, A2, B2, p2))
    family[str(t)] = {"Ta": A2, "Tb": B2, "pi": p2, "same_process": same_law}
    C.check(f"hmm_family_member_valid[t={t}]", same_law)


def iso(r1, r2):
    _, A1, B1, p1 = r1
    _, A2, B2, p2 = r2
    if (A1, B1, p1) == (A2, B2, p2):
        return True
    sw = lambda M: [[M[1][1], M[1][0]], [M[0][1], M[0][0]]]
    return (sw(A1), sw(B1), p1[::-1]) == (A2, B2, p2)


C.check("hmm_family_pairwise_non_isomorphic",
        all(not iso(reps[i], reps[j]) for i in range(len(reps)) for j in range(len(reps)) if i != j))
# the valid parameter interval is [(3-sqrt17)/2, (sqrt17-3)/4]; just outside it the transform is not a valid HMM
def valid(t):
    A2, B2, p2 = transformed(t)
    return all(v >= 0 for r in A2 + B2 for v in r) and all(v >= 0 for v in p2)
C.check("hmm_family_boundary", valid(F(28, 100)) and not valid(F(29, 100)) and valid(F(-56, 100))
        and not valid(F(-57, 100)))

# complete-NFA gap: V(w)=0 iff w starts with b. The death language b.Sigma* has a 2-state NFA
# (with an empty transition set), but every exact universal presentation (nonempty transitions) needs 3 states.
startb = DFA(ALPH, ["s", "ok", "dead"], "s",
             {("s", "a"): "ok", ("s", "b"): "dead", ("ok", "a"): "ok", ("ok", "b"): "ok",
              ("dead", "a"): "dead", ("dead", "b"): "dead"}, accept={"s", "ok"})
ex2, cnt2 = exhaustive_exists(2, startb)
ex3b, cnt3b = exhaustive_exists(3, startb)
C.check("universal_size_can_exceed_nfa_size_by_one", (not ex2) and ex3b, {"m2_candidates": cnt2})

out["hmm_family"] = family

out["checks"] = C.results
out["all_checks_pass"] = C.all_pass()
d = write_receipt("r5_presentations.json", out)
print("R5 all_checks_pass =", C.all_pass(), "digest", d)
