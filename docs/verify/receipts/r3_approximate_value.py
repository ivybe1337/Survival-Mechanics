"""
Receipt R3 -- approximate residual state (value bounds).

Planning (the agent chooses every symbol), monotone admissibility rule V, reward r(h,e) in [0,1]
collected at step t only if the history is still alive after step t, discount gamma in (0,1).

  W_Pi(h)   = sup over plans z in Pi of  sum_t gamma^(t-1) a_t(h,z) r(h z_<t, z_t)
  N_Pi(h,h')= first step at which survival status differs along some plan of Pi
  Delta_t   = sup over plans of Pi of the step-t reward disagreement

Theorem checked:  |W_Pi(h) - W_Pi(h')| <= sum_{t<N} gamma^(t-1) Delta_t + gamma^(N-1)/(1-gamma),
with N = N_Pi(h,h') >= N_kappa(h,h'), and equality in the countdown construction.
Also checked: the Bellman fixed point D on pairs dominates |W(h)-W(h')| and is dominated by the bound.

Stochastic (the world emits symbols from a process P):
  U(h) = E[ sum_t gamma^(t-1) a_t r ]
  (a) coupling metric fixed point dominates |U(h)-U(h')|
  (b) if eps(h)=eps(h'): |U(h)-U(h')| <= E[gamma^(tau-1)]/(1-gamma), tau = first time survival status differs,
      with equality in the countdown construction.
All values solved exactly (policy iteration / linear solves over Fractions).
"""
from fractions import Fraction as F
from itertools import product

from la_core import AVOID_BB, DFA, Checks, dfa_avoid, iid, parity_bernoulli, words, write_receipt

ALPH = ("a", "b")
C = Checks()
out = {}


# ---------------------------------------------------------------- exact linear algebra
def solve(A, b):
    n = len(A)
    M = [list(A[i]) + [b[i]] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [M[r][k] - f * M[c][k] for k in range(n + 1)]
    return [M[i][n] for i in range(n)]


def policy_iteration(states, actions, step, reward, gamma):
    """max-plus deterministic discounted problem: V(s) = max_a reward(s,a) + gamma V(step(s,a))."""
    idx = {s: i for i, s in enumerate(states)}
    pol = {s: actions[0] for s in states}
    while True:
        A = [[F(0)] * len(states) for _ in states]
        b = [F(0)] * len(states)
        for s in states:
            i = idx[s]
            A[i][i] += 1
            A[i][idx[step(s, pol[s])]] -= gamma
            b[i] = reward(s, pol[s])
        Vv = solve(A, b)
        val = {s: Vv[idx[s]] for s in states}
        changed = False
        for s in states:
            best = max(actions, key=lambda a: (reward(s, a) + gamma * val[step(s, a)], a == pol[s]))
            if reward(s, best) + gamma * val[step(s, best)] > reward(s, pol[s]) + gamma * val[step(s, pol[s])]:
                pol[s] = best
                changed = True
        if not changed:
            return val


# ---------------------------------------------------------------- product machines
class Product:
    """Joint machine: (eps-state of a unifilar process given as phase counter, DFA state)."""

    def __init__(self, dfa, period, rtilde):
        self.D, self.k, self.rt = dfa, period, rtilde
        self.states = sorted({(i, s) for i in range(period) for s in dfa.states}, key=repr)

    def start(self):
        return (0, self.D.start)

    def step(self, st, e):
        return ((st[0] + 1) % self.k, self.D.delta[(st[1], e)])

    def alive(self, st):
        return 1 if st[1] in self.D.accept else 0

    def c(self, st, e):
        nxt = self.step(st, e)
        return self.alive(nxt) * self.rt(st[0], e)

    def of(self, h):
        st = self.start()
        for e in h:
            st = self.step(st, e)
        return st


def countdown(N):
    """V(w)=1 iff w does not start with b, or |w| <= N.  Monotone."""
    states = ["S", "A", "X"] + [f"B{i}" for i in range(1, N + 1)]
    d = {("S", "a"): "A", ("S", "b"): "B1"}
    for e in ALPH:
        d[("A", e)] = "A"
        d[("X", e)] = "X"
        for i in range(1, N + 1):
            d[(f"B{i}", e)] = f"B{i + 1}" if i < N else "X"
    return DFA(ALPH, states, "S", d, accept={"S", "A"} | {f"B{i}" for i in range(1, N + 1)})


def N_kappa(D, s, t, cap=200):
    """Shortest z with V(s z) != V(t z) (BFS on DFA pairs); None if equivalent."""
    if (s in D.accept) != (t in D.accept):
        return 0
    seen = {(s, t)}
    frontier = [(s, t)]
    depth = 0
    while frontier and depth < cap:
        depth += 1
        nxt = []
        for (x, y) in frontier:
            for e in ALPH:
                u, v = D.delta[(x, e)], D.delta[(y, e)]
                if (u in D.accept) != (v in D.accept):
                    return depth
                if (u, v) not in seen:
                    seen.add((u, v))
                    nxt.append((u, v))
        frontier = nxt
    return None


def exact_discounted(state0, step_fn, val_fn, gamma, T=None):
    """sum_{t=1}^{T} gamma^(t-1) val_fn(state_t), state_1 = state0, state_{t+1} = step_fn(state_t).
    T=None means an infinite sum; the state space is finite, so the sequence is eventually periodic and
    the sum is computed exactly by cycle detection."""
    if T is not None:
        tot, st = F(0), state0
        for t in range(1, T + 1):
            tot += gamma ** (t - 1) * val_fn(st)
            st = step_fn(st)
        return tot
    seen, seq, st = {}, [], state0
    while st not in seen:
        seen[st] = len(seq)
        seq.append(val_fn(st))
        st = step_fn(st)
    mu = seen[st]
    tot = sum(gamma ** t * seq[t] for t in range(mu))
    L = len(seq) - mu
    cyc = sum(gamma ** (t - mu) * seq[t] for t in range(mu, len(seq)))
    return tot + gamma ** mu * cyc / (1 - gamma ** L)


def bound(M, s, t, gamma, N):
    """sum_{t<N} gamma^(t-1) Delta_t + gamma^(N-1)/(1-gamma), Delta_t = max reward disagreement over
    all common plans at step t.  N=None means kappa-equivalent: the bound is sum_t gamma^(t-1) Delta_t."""
    step_fn = lambda P: frozenset((M.step(x, e), M.step(y, e)) for (x, y) in P for e in ALPH)
    val_fn = lambda P: max(abs(M.rt(x[0], e) - M.rt(y[0], e)) for (x, y) in P for e in ALPH)
    P0 = frozenset({(s, t)})
    if N is None:
        return exact_discounted(P0, step_fn, val_fn, gamma)
    return exact_discounted(P0, step_fn, val_fn, gamma, T=N - 1) + gamma ** (N - 1) / (1 - gamma)


# ---------------------------------------------------------------- deterministic planning
rtildes = {
    "r_one": lambda ph, e: F(1),
    "r_phase": lambda ph, e: {(0, "a"): F(1), (0, "b"): F(1, 2), (1, "a"): F(0), (1, "b"): F(1)}[(ph, e)],
}
rules = {"avoid_bb": AVOID_BB, "avoid_aab": dfa_avoid("aab"), "countdown_3": countdown(3)}
det_report = {}
for (rn, D), (wn, rt), gamma in product(rules.items(), rtildes.items(), (F(1, 2), F(3, 4))):
    M = Product(D, 2, rt)
    W = policy_iteration(M.states, ALPH, M.step, M.c, gamma)
    pair_states = [(x, y) for x in M.states for y in M.states]
    Dfix = policy_iteration(pair_states, ALPH, lambda p, e: (M.step(p[0], e), M.step(p[1], e)),
                            lambda p, e: abs(M.c(p[0], e) - M.c(p[1], e)), gamma)
    viol_W_D, viol_D_B, n = 0, 0, 0
    for (x, y) in pair_states:
        if M.alive(x) != M.alive(y):
            continue
        n += 1
        if abs(W[x] - W[y]) > Dfix[(x, y)]:
            viol_W_D += 1
        Nk = N_kappa(D, x[1], y[1])
        if Dfix[(x, y)] > bound(M, x, y, gamma, Nk):
            viol_D_B += 1
    key = f"{rn}|{wn}|gamma={gamma}"
    det_report[key] = {"pairs": n, "W_le_D_violations": viol_W_D, "D_le_bound_violations": viol_D_B}
    C.check(f"planning_bound[{key}]", viol_W_D == 0 and viol_D_B == 0, det_report[key])
out["planning"] = det_report

# tightness: countdown, r = 1
tight = {}
for N in range(1, 7):
    for gamma in (F(1, 2), F(3, 4)):
        D = countdown(N)
        M = Product(D, 1, rtildes["r_one"])
        W = policy_iteration(M.states, ALPH, M.step, M.c, gamma)
        a, b = M.of("a"), M.of("b")
        Nk = N_kappa(D, a[1], b[1])
        gap = W[a] - W[b]
        B = gamma ** (Nk - 1) / (1 - gamma)
        tight[f"N={N},gamma={gamma}"] = {"N_kappa": Nk, "gap": gap, "bound": B}
        C.check(f"planning_tight[N={N},gamma={gamma}]", Nk == N and gap == B)
out["planning_tightness"] = tight

# plan-family restriction: Pi = eventually periodic plans from a finite list
def plan_value(M, st, plan, gamma):
    """Exact discounted value of an eventually periodic plan (prefix u, cycle v)."""
    u, v = plan
    total, disc = F(0), F(1)
    for e in u:
        total += disc * M.c(st, e)
        st = M.step(st, e)
        disc *= gamma
    seen = {}
    cyc_vals = []
    while st not in seen:
        seen[st] = len(cyc_vals)
        val, d2 = F(0), F(1)
        s2 = st
        for e in v:
            val += d2 * M.c(s2, e)
            s2 = M.step(s2, e)
            d2 *= gamma
        cyc_vals.append((val, st))
        st = s2
    start = seen[st]
    g = gamma ** len(v)
    for i, (val, _) in enumerate(cyc_vals[:start]):
        total += disc * val
        disc *= g
    loop = cyc_vals[start:]
    loop_sum = F(0)
    dd = F(1)
    for val, _ in loop:
        loop_sum += dd * val
        dd *= g
    total += disc * loop_sum / (1 - dd)
    return total


def plan_symbols(plan, T):
    u, v = plan
    s = u
    while len(s) < T:
        s += v
    return s[:T]


FAMILIES = {"mixed": [("", "a"), ("", "ab"), ("b", "a"), ("ab", "aab"), ("a", "b")],
            "cautious": [("", "a"), ("a", "ba")]}
restr = {}
for (fam, PI), (rn, D), (wn, rt) in product(FAMILIES.items(), rules.items(), rtildes.items()):
    gamma = F(3, 4)
    M = Product(D, 2, rt)
    hs = words(ALPH, 4)
    viol, cnt, stricter = 0, 0, 0
    for h, h2 in product(hs, hs):
        x, y = M.of(h), M.of(h2)
        if M.alive(x) != M.alive(y) or not M.alive(x):
            continue
        cnt += 1
        WPi = max(plan_value(M, x, p, gamma) for p in PI)
        WPi2 = max(plan_value(M, y, p, gamma) for p in PI)
        # joint deterministic state: for every plan, (state_x, state_y, position); exact cycle detection
        def pos_next(p, i):
            u, v = PI[p]
            return i + 1 if i + 1 < len(u) + len(v) else len(u)

        def sym(p, i):
            u, v = PI[p]
            return (u + v)[i]

        J0 = tuple((x, y, 0) for p in range(len(PI)))
        stepJ = lambda Js: tuple((M.step(sx, sym(p, i)), M.step(sy, sym(p, i)), pos_next(p, i))
                                 for p, (sx, sy, i) in enumerate(Js))
        valDelta = lambda Js: max(abs(rt(sx[0], sym(p, i)) - rt(sy[0], sym(p, i)))
                                  for p, (sx, sy, i) in enumerate(Js))
        # first disagreement time N_Pi (search until the joint state repeats)
        NPi, Js, seenJ, t = None, J0, set(), 0
        while Js not in seenJ:
            seenJ.add(Js)
            t += 1
            Js2 = stepJ(Js)
            if any(M.alive(a) != M.alive(b) for (a, b, _) in Js2):
                NPi = t
                break
            Js = Js2
        if NPi is None:
            B = exact_discounted(J0, stepJ, valDelta, gamma)
        else:
            B = exact_discounted(J0, stepJ, valDelta, gamma, T=NPi - 1) + gamma ** (NPi - 1) / (1 - gamma)
        if abs(WPi - WPi2) > B:
            viol += 1
        Nk = N_kappa(D, x[1], y[1])
        if Nk is not None and NPi is not None and NPi < Nk:
            viol += 1
        if Nk is not None and (NPi is None or NPi > Nk):
            stricter += 1
    restr[f"{fam}|{rn}|{wn}"] = {"pairs": cnt, "violations": viol, "pairs_where_N_Pi_exceeds_N_kappa": stricter}
    C.check(f"restricted_family_bound[{fam}|{rn}|{wn}]", viol == 0, restr[f"{fam}|{rn}|{wn}"])
out["plan_family"] = restr
C.check("restriction_strictly_delays_detection_somewhere",
        any(v["pairs_where_N_Pi_exceeds_N_kappa"] > 0 for v in restr.values()))


# ---------------------------------------------------------------- stochastic setting
def stochastic(D, P_period_biases, rt, gamma):
    """World emits symbols from a phase-Bernoulli process; returns (states, U, step, prob)."""
    k = len(P_period_biases)
    M = Product(D, k, rt)
    prob = lambda st, e: F(P_period_biases[st[0]]) if e == "a" else 1 - F(P_period_biases[st[0]])
    idx = {s: i for i, s in enumerate(M.states)}
    A = [[F(0)] * len(M.states) for _ in M.states]
    b = [F(0)] * len(M.states)
    for s in M.states:
        i = idx[s]
        A[i][i] += 1
        for e in ALPH:
            A[i][idx[M.step(s, e)]] -= gamma * prob(s, e)
            b[i] += prob(s, e) * M.c(s, e)
    Uv = solve(A, b)
    return M, {s: Uv[idx[s]] for s in M.states}, prob


stoch = {}
for (rn, D), (wn, rt), biases in product(rules.items(), rtildes.items(),
                                          ([F(1, 2)], [F(9, 10), F(1, 10)], [F(2, 3), F(1, 5)], [F(1), F(1, 2)], [F(1, 3), F(0)])):
    gamma = F(3, 4)
    M, U, prob = stochastic(D, biases, rt, gamma)
    pairs = [(x, y) for x in M.states for y in M.states]
    pidx = {p: i for i, p in enumerate(pairs)}
    Mbig = F(1) / (1 - gamma)
    # coupling metric: D(x,y) = TV/(1-g) + sum_e P(e|y)[|c(x,e)-c(y,e)| + g D(xe,ye)]
    A = [[F(0)] * len(pairs) for _ in pairs]
    bb = [F(0)] * len(pairs)
    for (x, y) in pairs:
        i = pidx[(x, y)]
        A[i][i] += 1
        tvv = sum(abs(prob(x, e) - prob(y, e)) for e in ALPH) / 2
        bb[i] += tvv * Mbig
        for e in ALPH:
            if prob(x, e) == 0 or prob(y, e) == 0:
                continue  # symbols impossible for one side contribute only through the TV term
            A[i][pidx[(M.step(x, e), M.step(y, e))]] -= gamma * prob(y, e)
            bb[i] += prob(y, e) * abs(M.c(x, e) - M.c(y, e))
    Dv = solve(A, bb)
    Dc = {p: Dv[pidx[p]] for p in pairs}
    # time-to-distinguish functional for same-eps pairs: G(x,y) = sum_e P(e|x)[diff + same*g*G]
    same = [(x, y) for (x, y) in pairs if x[0] == y[0]]
    sidx = {p: i for i, p in enumerate(same)}
    A2 = [[F(0)] * len(same) for _ in same]
    b2 = [F(0)] * len(same)
    for (x, y) in same:
        i = sidx[(x, y)]
        A2[i][i] += 1
        for e in ALPH:
            xe, ye = M.step(x, e), M.step(y, e)
            if M.alive(xe) != M.alive(ye):
                b2[i] += prob(x, e)
            else:
                A2[i][sidx[(xe, ye)]] -= gamma * prob(x, e)
    Gv = solve(A2, b2)
    G = {p: Gv[sidx[p]] for p in same}
    v1 = sum(1 for (x, y) in pairs if M.alive(x) == M.alive(y) and abs(U[x] - U[y]) > min(Dc[(x, y)], Dc[(y, x)]))
    v2 = sum(1 for (x, y) in same if M.alive(x) == M.alive(y) and abs(U[x] - U[y]) > G[(x, y)] / (1 - gamma))
    key = f"{rn}|{wn}|biases={[str(b) for b in biases]}"
    diag0 = all(Dc[(x, x)] == 0 for x in M.states)
    stoch[key] = {"coupling_violations": v1, "time_to_distinguish_violations": v2, "diagonal_zero": diag0}
    C.check(f"stochastic_bounds[{key}]", v1 == 0 and v2 == 0 and diag0, stoch[key])
out["stochastic"] = stoch

tight2 = {}
for N in range(1, 7):
    gamma = F(3, 4)
    D = countdown(N)
    M, U, prob = stochastic(D, [F(1, 3)], rtildes["r_one"], gamma)
    a, b = M.of("a"), M.of("b")
    # tau = N deterministically for (a, b): statuses agree until b-branch dies at step N
    Gab = gamma ** (N - 1)
    gap = U[a] - U[b]
    tight2[f"N={N}"] = {"gap": gap, "bound": Gab / (1 - gamma)}
    C.check(f"stochastic_tight[N={N}]", gap == Gab / (1 - gamma))
out["stochastic_tightness"] = tight2

out["checks"] = C.results
out["all_checks_pass"] = C.all_pass()
d = write_receipt("r3_approximate_value.json", out)
print("R3 all_checks_pass =", C.all_pass(), "digest", d)
