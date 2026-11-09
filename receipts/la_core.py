"""
Shared exact-arithmetic utilities for the Likely and Allowed receipts.

Everything here is integer / Fraction arithmetic. No floats, no randomness.
Words are Python strings over a finite alphabet; the empty word is "".
"""
from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from itertools import product

F = Fraction


# ---------------------------------------------------------------- words

def words(alphabet, max_len, min_len=0):
    out = []
    for n in range(min_len, max_len + 1):
        for t in product(alphabet, repeat=n):
            out.append("".join(t))
    return out


# ---------------------------------------------------------------- DFAs / admissibility rules

class DFA:
    """Complete DFA. accept = set of states where V = 1."""

    def __init__(self, alphabet, states, start, delta, accept):
        self.alphabet = tuple(alphabet)
        self.states = tuple(states)
        self.start = start
        self.delta = dict(delta)
        self.accept = frozenset(accept)
        for s in self.states:
            for a in self.alphabet:
                assert (s, a) in self.delta, (s, a)

    def run(self, w, s=None):
        s = self.start if s is None else s
        for a in w:
            s = self.delta[(s, a)]
        return s

    def V(self, w):
        return 1 if self.run(w) in self.accept else 0

    def reachable(self):
        seen = {self.start}
        frontier = [self.start]
        while frontier:
            nxt = []
            for s in frontier:
                for a in self.alphabet:
                    t = self.delta[(s, a)]
                    if t not in seen:
                        seen.add(t)
                        nxt.append(t)
            frontier = nxt
        return seen

    def nerode_blocks(self):
        """Moore partition refinement on reachable states. Returns dict state -> block id."""
        R = sorted(self.reachable(), key=repr)
        block = {s: (1 if s in self.accept else 0) for s in R}
        while True:
            sig = {s: (block[s],) + tuple(block[self.delta[(s, a)]] for a in self.alphabet) for s in R}
            ids = {}
            new = {}
            for s in R:
                if sig[s] not in ids:
                    ids[sig[s]] = len(ids)
                new[s] = ids[sig[s]]
            if len(set(new.values())) == len(set(block.values())):
                return new
            block = new

    def kappa(self, w):
        return self.nerode_blocks()[self.run(w)]

    def index(self):
        return len(set(self.nerode_blocks().values()))


def residual_row(V, h, suffixes):
    return tuple(V(h + z) for z in suffixes)


# ---------------------------------------------------------------- processes (edge-emitting HMMs)

class HMM:
    """Edge-emitting hidden Markov model with exact rational parameters.
    pi: list of Fractions (initial distribution over m states)
    T:  dict symbol -> m x m matrix (list of lists of Fractions), T[x][i][j] = P(emit x, go to j | i).
    Rows of sum_x T[x] must sum to 1.
    """

    def __init__(self, alphabet, pi, T):
        self.alphabet = tuple(alphabet)
        self.pi = [F(x) for x in pi]
        self.m = len(self.pi)
        self.T = {x: [[F(v) for v in row] for row in T[x]] for x in self.alphabet}
        assert sum(self.pi) == 1 and all(v >= 0 for v in self.pi)
        for i in range(self.m):
            tot = sum(self.T[x][i][j] for x in self.alphabet for j in range(self.m))
            assert tot == 1, ("row not stochastic", i, tot)
            for x in self.alphabet:
                assert all(v >= 0 for v in self.T[x][i])

    def vec_after(self, w, v=None):
        v = list(self.pi) if v is None else list(v)
        for x in w:
            M = self.T[x]
            v = [sum(v[i] * M[i][j] for i in range(self.m)) for j in range(self.m)]
        return v

    def p(self, w):
        return sum(self.vec_after(w))

    def future(self, h):
        """Normalized state-belief row vector after h, or None if p(h) = 0."""
        v = self.vec_after(h)
        s = sum(v)
        if s == 0:
            return None
        return [x / s for x in v]

    def P_h(self, h, z):
        """Conditional probability of continuation z given h (h must have positive probability)."""
        u = self.future(h)
        assert u is not None
        return sum(self.vec_after(z, u))

    # --- exact causal-state test via the right-reachable subspace span{T^z 1}
    def right_basis(self):
        if hasattr(self, "_rb"):
            return self._rb
        one = [F(1)] * self.m
        basis = []  # list of vectors in reduced echelon-ish form (kept raw), plus pivots
        queue = [one]
        reduced = []  # (pivot, vector)

        def reduce(v):
            v = list(v)
            for piv, b in reduced:
                if v[piv] != 0:
                    c = v[piv] / b[piv]
                    v = [v[k] - c * b[k] for k in range(self.m)]
            return v

        while queue:
            v = queue.pop(0)
            r = reduce(v)
            nz = [k for k in range(self.m) if r[k] != 0]
            if not nz:
                continue
            reduced.append((nz[0], r))
            basis.append(v)
            for x in self.alphabet:
                M = self.T[x]
                queue.append([sum(M[i][j] * v[j] for j in range(self.m)) for i in range(self.m)])
        self._rb = basis
        return basis

    def eps_signature(self, h):
        """A canonical, exact signature of the causal state of h:
        the vector of pairings of the normalized belief with a basis of span{T^z 1}.
        Two histories have the same future law iff signatures are equal. None for null histories."""
        u = self.future(h)
        if u is None:
            return None
        return tuple(sum(u[i] * b[i] for i in range(self.m)) for b in self.right_basis())


def partition(items, key):
    blocks = {}
    for it in items:
        blocks.setdefault(key(it), []).append(it)
    return sorted((sorted(b) for b in blocks.values()), key=lambda b: (len(b[0]), b[0]))


def refines(fine, coarse):
    """True iff every block of `fine` lies inside a block of `coarse` (both lists of lists)."""
    where = {}
    for i, b in enumerate(coarse):
        for x in b:
            where[x] = i
    return all(len({where[x] for x in b}) == 1 for b in fine)


# ---------------------------------------------------------------- receipts

def jsonable(o):
    if isinstance(o, Fraction):
        return f"{o.numerator}/{o.denominator}" if o.denominator != 1 else str(o.numerator)
    if isinstance(o, dict):
        return {str(k): jsonable(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [jsonable(v) for v in o]
    if isinstance(o, (set, frozenset)):
        return sorted(jsonable(v) for v in o)
    return o


def write_receipt(path, payload):
    payload = jsonable(payload)
    body = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    digest = hashlib.sha256(body.encode()).hexdigest()
    payload["receipt_sha256_without_hash_field"] = digest
    with open(path, "w") as fh:
        json.dump(payload, fh, indent=2, sort_keys=True)
    return digest


class Checks:
    def __init__(self):
        self.results = {}

    def check(self, name, cond, detail=None):
        self.results[name] = {"pass": bool(cond)} if detail is None else {"pass": bool(cond), "detail": detail}
        if not cond:
            print("FAIL:", name, detail)
        return cond

    def all_pass(self):
        return all(v["pass"] for v in self.results.values())


# ---------------------------------------------------------------- standard examples

def dfa_avoid(factor, alphabet=("a", "b")):
    """DFA for 'the word never contains `factor`' (KMP automaton + dead state)."""
    k = len(factor)
    states = list(range(k + 1))  # k = dead
    delta = {}
    for s in range(k):
        for a in alphabet:
            cand = factor[:s] + a
            while cand and not factor.startswith(cand):
                cand = cand[1:]
            t = len(cand)
            delta[(s, a)] = t  # t == k means factor seen -> dead
    for a in alphabet:
        delta[(k, a)] = k
    return DFA(alphabet, states, 0, delta, accept=set(range(k)))


AVOID_BB = dfa_avoid("bb")


def parity_bernoulli(bias_even, bias_odd, alphabet=("a", "b")):
    """Independent symbols; P(a) = bias_even at even positions (0-indexed), bias_odd at odd positions."""
    a, b = alphabet
    be, bo = F(bias_even), F(bias_odd)
    T = {a: [[0, be], [bo, 0]], b: [[0, 1 - be], [1 - bo, 0]]}
    return HMM(alphabet, [1, 0], T)


def phase_bernoulli(biases, alphabet=("a", "b")):
    """Period-k independent process: P(a) at position t is biases[t mod k]."""
    k = len(biases)
    a, b = alphabet
    Ta = [[F(0)] * k for _ in range(k)]
    Tb = [[F(0)] * k for _ in range(k)]
    for i in range(k):
        Ta[i][(i + 1) % k] = F(biases[i])
        Tb[i][(i + 1) % k] = 1 - F(biases[i])
    return HMM(alphabet, [1] + [0] * (k - 1), {a: Ta, b: Tb})


def iid(pa, alphabet=("a", "b")):
    a, b = alphabet
    return HMM(alphabet, [1], {a: [[F(pa)]], b: [[1 - F(pa)]]})
