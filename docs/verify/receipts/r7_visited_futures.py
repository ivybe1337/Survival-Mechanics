"""
Receipt R7 -- Corollary (what the forecasts see without full support).

Claim checked: for h, h' in Supp(p),  Psi_H(h) = Psi_H(h')  iff  P_h = P_h' on words of length <= H
and  Res(h) & Supp(P_h) = Res(h') & Supp(P_h')  on words of length <= H.
Psi_H(h) = (P_h on words of length <= H, S_n(h) and Q_n(.|h) for n <= H).

Instances: random Markov chains on {a,b,c} with forced zero transitions (so Supp(p) is a proper subset),
random survival functions V on all words of length <= 7 (no monotonicity assumed; the corollary does not use it).
Exact rational arithmetic.
"""
import itertools
import random
from fractions import Fraction as F

from la_core import Checks, write_receipt

ALPH = ("a", "b", "c")
H = 3
L = 7


def words(n):
    return ["".join(t) for t in itertools.product(ALPH, repeat=n)]


def make_chain(rng):
    init = {x: F(rng.randint(1, 4)) for x in ALPH}
    tot = sum(init.values())
    init = {x: v / tot for x, v in init.items()}
    T = {}
    for x in ALPH:
        w = {y: (F(0) if rng.random() < 0.45 else F(rng.randint(1, 5))) for y in ALPH}
        if sum(w.values()) == 0:
            w[rng.choice(ALPH)] = F(1)
        s = sum(w.values())
        T[x] = {y: v / s for y, v in w.items()}
    return init, T


def prob(init, T, w):
    if not w:
        return F(1)
    p = init[w[0]]
    for x, y in zip(w, w[1:]):
        p *= T[x][y]
    return p


def run(seed):
    rng = random.Random(seed)
    init, T = make_chain(rng)
    V = {}
    for n in range(L + 1):
        for w in words(n):
            V[w] = 1 if rng.random() < 0.55 else 0
    hist = [h for n in range(0, 3) for h in words(n) if prob(init, T, h) > 0]
    fut = [z for n in range(0, H + 1) for z in words(n)]

    def Ph(h):
        ph = prob(init, T, h)
        return {z: prob(init, T, h + z) / ph for z in fut}

    def Psi(h):
        P = Ph(h)
        out = [tuple(sorted(P.items()))]
        for n in range(0, H + 1):
            Z = [z for z in fut if len(z) == n]
            S = sum(P[z] for z in Z if V[h + z])
            if S == 0:
                out.append((n, S, None))
            else:
                out.append((n, S, tuple((z, P[z] * V[h + z] / S) for z in Z)))
        return tuple(out)

    def kp(h):
        P = Ph(h)
        return (tuple(sorted(P.items())), frozenset(z for z in fut if P[z] > 0 and V[h + z]))

    n_pairs = n_blind = 0
    ok = True
    for h, g in itertools.combinations(hist, 2):
        lhs = Psi(h) == Psi(g)
        rhs = kp(h) == kp(g)
        ok &= (lhs == rhs)
        n_pairs += 1
        # pairs with equal P_h and different full residual on unvisited futures (the blind spot is nonempty)
        if Ph(h) == Ph(g) and lhs:
            Rh = frozenset(z for z in fut if V[h + z])
            Rg = frozenset(z for z in fut if V[g + z])
            if Rh != Rg:
                n_blind += 1
    return ok, n_pairs, n_blind


C = Checks()
tot_pairs = tot_blind = 0
all_ok = True
for seed in range(60):
    ok, npairs, nblind = run(seed)
    all_ok &= ok
    tot_pairs += npairs
    tot_blind += nblind
C.check("psi_equal_iff_eps_equal_and_visited_residual_equal", all_ok)
C.check("blind_spot_is_realized (pairs with equal Psi but different Res exist)", tot_blind > 0)
out = {"seeds": 60, "horizon": H, "pairs_checked": tot_pairs, "pairs_with_nonempty_blind_spot": tot_blind,
       "checks": C.results, "all_checks_pass": C.all_pass()}
d = write_receipt("r7_visited_futures.json", out)
print("R7 all_checks_pass =", C.all_pass(), "pairs", tot_pairs, "blind", tot_blind, "digest", d)
