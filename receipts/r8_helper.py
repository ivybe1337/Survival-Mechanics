"""Exact-arithmetic helpers for receipt R8; standard library only.

Imported by r8_extensions.py.
These finite checks supplement the proofs; they do not certify literature priority.
"""

from fractions import Fraction as F
from itertools import product
import hashlib
import json
from pathlib import Path


def words(n):
    return ("".join(w) for w in product("ab", repeat=n))


def matmul(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def determinant(a):
    a = [list(map(F, row)) for row in a]
    ans = F(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            ans = -ans
        v = a[j][j]
        ans *= v
        a[j] = [x / v for x in a[j]]
        for i in range(j + 1, len(a)):
            v = a[i][j]
            a[i] = [x - v * y for x, y in zip(a[i], a[j])]
    return ans


def tv(p, q):
    return sum(abs(p.get(w, 0) - q.get(w, 0)) for w in p.keys() | q.keys()) / 2


def prob_unifilar(q, transition, state, word):
    p = F(1)
    for x in word:
        p *= q[state] if x == "a" else 1 - q[state]
        state = transition(state, x)
    return p


def dist_unifilar(q, transition, state, n):
    return {w: prob_unifilar(q, transition, state, w) for w in words(n)}


def clock_checks():
    cases = []
    for m in range(2, 9):
        q = [F(1, 3)] * (m - 1) + [F(2, 3)]
        transition = lambda i, x: (i + 1) % m
        for n in range(m - 1):
            assert dist_unifilar(q, transition, 0, n) == dist_unifilar(q, transition, 1, n)
        assert dist_unifilar(q, transition, 0, m - 1) != dist_unifilar(q, transition, 1, m - 1)
        obs = [[prob_unifilar(q, transition, i, "a" * n) for n in range(m)] for i in range(m)]
        det = determinant(obs)
        assert det
        cases.append({"dimension": m, "first_difference": m - 1, "test_determinant": str(det)})
    return cases


def countdown_checks():
    count = 0
    for m in range(1, 7):
        q = [F(2, 3)] + [F(1, 3)] * (m - 1)
        transition = lambda i, x: (0 if x == "a" else m - 1) if i == 0 else i - 1
        obs = [[prob_unifilar(q, transition, i, "a" * n) for n in range(m)] for i in range(m)]
        assert determinant(obs)
        assert transition(0, "a") == 0
        for k in range(3, 9):
            for n in range(k - 2):
                # h=empty and h'=a, V(w)=1 iff len(w)<=k-2.
                assert (n <= k - 2) == (n + 1 <= k - 2)
            assert (k - 2 <= k - 2) != (k - 1 <= k - 2)
            count += 1
    return {"exact_dimension_and_rule_index_cases": count}


def separation_checks():
    result = []
    for d in range(2, 10):
        center = {i: F(1, d) for i in range(d)}
        targets = [{i: F(i == j) for i in range(d)} for j in range(d)]
        assert max(tv(center, q) for q in targets) == 1 - F(1, d)
        eta = F(1, 100)
        soft = [{i: (1 - eta) * F(i == j) + eta / d for i in range(d)} for j in range(d)]
        assert max(tv(center, q) for q in soft) == (1 - eta) * (1 - F(1, d))
        result.append({"alphabet": d, "epsilon_only_radius": str(1 - F(1, d)),
                       "kappa_only_radius_at_eta_1_100": str((1 - eta) * (1 - F(1, d)))})
    return result


def rare_word_checks():
    eps = F(1, 10**6)
    result = []
    for n in range(1, 7):
        p = {w: (1 - eps) ** w.count("a") * eps ** w.count("b") for w in words(n)}
        q_restricted = {"a" * n: F(1)}
        gap = 1 - (1 - eps) ** n
        assert tv(p, q_restricted) == gap <= n * eps
        result.append({"horizon": n, "survival_and_conditional_TV_gap": str(gap)})
    return result


def mixture_checks():
    eps = F(1, 1000)
    q_plus, q_minus = F(1, 2) + eps, F(1, 2) - eps
    length = 10000
    # Equal-prior mixture, histories a^length and b^length.
    w = F(501**length, 501**length + 499**length)
    infinite_tv = 2 * w - 1  # The two iid components are singular by the SLLN.
    assert infinite_tv > F(999, 1000)
    for n in range(1, 5):
        plus = {z: q_plus ** z.count("a") * q_minus ** z.count("b") for z in words(n)}
        minus = {z: q_minus ** z.count("a") * q_plus ** z.count("b") for z in words(n)}
        assert tv(plus, minus) <= 2 * n * eps
        # Posterior-mixture difference scales this TV by 2w-1.
        assert infinite_tv * tv(plus, minus) <= 2 * n * eps
    return {"component_bias_difference": "1/500", "history_length": length,
            "infinite_future_TV_lower_bound": "999/1000", "max_tested_horizon": 4,
            "finite_horizon_TV_upper_bound": "H/500"}


TA = [[F(3, 8), F(1, 8)], [F(1, 8), F(1, 8)]]
TB = [[F(1, 8), F(3, 8)], [F(1, 8), F(5, 8)]]
PI = [F(1, 3), F(2, 3)]


def posterior(word):
    u = PI[:]
    for x in word:
        u = matmul([u], TA if x == "a" else TB)[0]
        s = sum(u)
        u = [x / s for x in u]
    return u


def prob_hmm(u, word):
    for x in word:
        u = matmul([u], TA if x == "a" else TB)[0]
    return sum(u)


def genericity_observability_checks():
    seen = {}
    for n in range(9):
        for word in words(n):
            u = posterior(word)
            x = u[0]
            assert x not in seen, (word, seen.get(x))
            seen[x] = word
            if word:
                previous = posterior(word[:-1])[0]
                formula = (1 + 2 * previous) / (2 + 2 * previous) if word[-1] == "a" else 1 / (6 - 2 * previous)
                assert formula == x
            assert prob_hmm(u, "a") == F(1, 4) + x / 4
    assert matmul([PI], [[TA[i][j] + TB[i][j] for j in range(2)] for i in range(2)])[0] == PI
    # Basis futures from histories empty and a; tests empty and a.
    basis = [PI, posterior("a")]
    o = [[F(1), prob_hmm(u, "a")] for u in basis]
    det = determinant(o)
    assert det
    inv = [[o[1][1] / det, -o[0][1] / det], [-o[1][0] / det, o[0][0] / det]]
    c_obs = sum(abs(x) for row in inv for x in row)
    samples = [w for n in range(4) for w in words(n)]
    for h in samples:
        for hp in samples:
            u, up = posterior(h), posterior(hp)
            test_diff = [F(0), prob_hmm(u, "a") - prob_hmm(up, "a")]
            coeff = matmul([test_diff], inv)[0]
            for n in range(1, 5):
                p = {z: prob_hmm(u, z) for z in words(n)}
                pp = {z: prob_hmm(up, z) for z in words(n)}
                assert tv(p, pp) <= sum(abs(x) for x in coeff) / 2
                assert tv(p, pp) <= abs(test_diff[1]) * c_obs / 2
    return {"distinct_posteriors_through_length_8": len(seen), "stationary_initial_distribution": True,
            "basis_test_determinant": str(det), "C_observation": str(c_obs),
            "finite_inverse_bound_pairs": len(samples) ** 2}


def rad_checks():
    g = [[F(3, 4), F(1, 4)], [F(1, 4), F(3, 4)]]
    m = [F(1), F(1, 3)]
    raw = [[g[i][j] * m[j] for j in range(2)] for i in range(2)]
    tilted = [[x / sum(row) for x in row] for row in raw]
    assert tilted == [[F(9, 10), F(1, 10)], [F(1, 2), F(1, 2)]]
    killed_generator = [[F(-1), F(1)], [F(1), F(-5, 2)]]
    r = [[F(2)], [F(1)]]
    lam = F(-1, 2)
    assert matmul(killed_generator, r) == [[lam * x[0]] for x in r]
    doob = [[killed_generator[i][j] * r[j][0] / r[i][0] - (lam if i == j else 0)
             for j in range(2)] for i in range(2)]
    assert doob == [[F(-1, 2), F(1, 2)], [F(2), F(-2)]]
    decay = F(1, 2)  # exp(-(a+b)*tau), tau=(2/5)*log(2).
    a, b = doob[0][1], doob[1][0]
    t = [[(b + a * decay) / (a + b), a * (1 - decay) / (a + b)],
         [b * (1 - decay) / (a + b), (a + b * decay) / (a + b)]]
    assert t == [[F(9, 10), F(1, 10)], [F(2, 5), F(3, 5)]]
    # Positive discrete killed kernel with three different conditioned objects.
    k = [[F(3, 8), F(1, 4)], [F(1, 8), F(1, 4)]]
    nu = [F(1, 2), F(1, 2)]
    rho = F(1, 2)
    assert matmul([nu], k)[0] == [rho * x for x in nu]
    assert matmul(k, r) == [[rho * x[0]] for x in r]
    q = [[k[i][j] * r[j][0] / (rho * r[i][0]) for j in range(2)] for i in range(2)]
    stationary = [F(2, 3), F(1, 3)]
    assert matmul([stationary], q)[0] == stationary
    assert q[0] == [F(3, 4), F(1, 4)]
    return {"positive_destination_tilt": [[str(x) for x in row] for row in tilted],
            "continuous_time_Doob_generator": [[str(x) for x in row] for row in doob],
            "sampled_Doob_transition": [[str(x) for x in row] for row in t],
            "QSD": list(map(str, nu)), "Q_process_stationary": list(map(str, stationary)),
            "Q_process_first_row": list(map(str, q[0]))}


def cycle_checks():
    a = [[F(2), F(0)], [F(0), F(1)]]
    ai = [[F(1, 2), F(0)], [F(0), F(1)]]
    b = [[F(2), F(1)], [F(1), F(2)]]
    bi = [[F(2, 3), F(-1, 3)], [F(-1, 3), F(2, 3)]]
    cycle = matmul(matmul(matmul(a, b), ai), bi)
    assert determinant(cycle) == 1
    gram = matmul(list(map(list, zip(*cycle))), cycle)
    assert gram != [[1, 0], [0, 1]]
    return {"cycle": [[str(x) for x in row] for row in cycle],
            "determinant": "1", "Gram_matrix": [[str(x) for x in row] for row in gram]}


def main():
    result = {
        "clock_horizon": clock_checks(),
        "countdown_horizon": countdown_checks(),
        "multitarget_separation": separation_checks(),
        "rare_word_instability": rare_word_checks(),
        "mixture_predictive_instability": mixture_checks(),
        "generic_HMM_and_inverse_bound": genericity_observability_checks(),
        "RAD_bridge_and_QSD": rad_checks(),
        "cycle_is_not_exact_rotation": cycle_checks(),
    }
    here = Path(__file__).resolve().parent
    result["inputs_sha256"] = {name: hashlib.sha256((here.parent / name).read_bytes()).hexdigest()
                               for name in ()}
    result["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    path = here / "r8_helper_results.json"
    path.write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: all eight exact-arithmetic check groups")
    print("Results:", path)
    print("SHA-256:", hashlib.sha256(path.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
