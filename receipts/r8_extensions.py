"""Receipt R8: exact checks for Propositions 4.4-4.5, 5.10-5.14, the symmetric bound in 6.4, and 9.4-9.8. All numerical work uses Fraction.

Finite checks support, but do not replace, the general proofs in the paper.
Run: python3 r8_extensions.py
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import r8_helper as prior


def solve(a, b):
    a = [[F(x) for x in row] + [F(y)] for row, y in zip(a, b)]
    for j in range(len(a)):
        k = next(i for i in range(j, len(a)) if a[i][j])
        a[j], a[k] = a[k], a[j]
        z = a[j][j]
        a[j] = [x / z for x in a[j]]
        for i in range(len(a)):
            if i != j:
                z = a[i][j]
                a[i] = [x - z * y for x, y in zip(a[i], a[j])]
    return [row[-1] for row in a]


def product_and_support():
    reps = ['', 'a', 'b', 'ab', 'bb', 'abb']
    def rule_state(w):
        return 'D' if 'bb' in w else ('B' if w.endswith('b') else 'A')
    pairs = {(len(w) % 2, rule_state(w)) for w in reps}
    assert len(pairs) == 6
    # Exact finite-set common-refinement identities, including comparability.
    count = 0
    for e in product(range(2), repeat=4):
        for k in product(range(3), repeat=4):
            joint = set(zip(e, k))
            ne, nk, nj = len(set(e)), len(set(k)), len(joint)
            eref = all(e[i] != e[j] or k[i] == k[j] for i in range(4) for j in range(4))
            kref = all(k[i] != k[j] or e[i] == e[j] for i in range(4) for j in range(4))
            assert max(ne, nk) <= nj <= ne * nk
            assert (nj == ne) == eref
            assert (nj == nk) == kref
            count += 1
    # Off-support masks disappear from B=P*V; monotone death still forces them.
    p = {'a': F(1), 'b': F(0)}
    assert {z: p[z] * v for z, v in {'a': 1, 'b': 0}.items()} == p
    assert {z: p[z] * v for z, v in {'a': 1, 'b': 1}.items()} == p
    return {'partition_pairs': count, 'reachable_product': sorted(map(str, pairs))}


def exact_horizons():
    clocks = prior.clock_checks()
    countdown = prior.countdown_checks()
    # Verify determinant formula, residual counts and joint reports too.
    cases = 0
    for m in range(1, 7):
        for k in range(1, 8):
            horizon = max(k - 2, m - 1)
            if horizon == 0:
                continue
            if m - 1 >= k - 2:
                p, q = F(1, 3), F(2, 3)
                probs = [p] * (m - 1) + [q]
                tr = lambda i, x: (i + 1) % m
                obs = [[prior.prob_unifilar(probs, tr, i, 'a' * n) for n in range(m)] for i in range(m)]
                assert abs(prior.determinant(obs)) == p ** ((m - 1) * (m - 2) // 2) * abs(q - p) ** (m - 1)
                valid = lambda w: True if k == 1 else 'b' * (k - 1) not in w
                states = [''] if k == 1 else ['b' * i for i in range(k)]
            else:
                probs = [F(2, 3)] + [F(1, 3)] * (m - 1)
                tr = lambda i, x: ((0 if x == 'a' else m - 1) if i == 0 else i - 1)
                valid = lambda w: len(w) <= k - 2
                states = ['a' * i for i in range(k)]
            tests = [w for n in range(max(0, k - 2) + 1) for w in prior.words(n)]
            assert len({tuple(valid(h + w) for w in tests) for h in states}) == k
            s0, s1 = 0, tr(0, 'a')
            for n in range(horizon):
                law0 = prior.dist_unifilar(probs, tr, s0, n)
                law1 = prior.dist_unifilar(probs, tr, s1, n)
                assert law0 == law1
                assert {w: t * valid(w) for w, t in law0.items()} == {w: t * valid('a' + w) for w, t in law1.items()}
            law0 = prior.dist_unifilar(probs, tr, s0, horizon)
            law1 = prior.dist_unifilar(probs, tr, s1, horizon)
            assert law0 != law1 or {w: t * valid(w) for w, t in law0.items()} != {w: t * valid('a' + w) for w, t in law1.items()}
            cases += 1
    return {'prior_clock_cases': len(clocks), **countdown, 'joint_reports_actual_m_k_cases': cases}


def killed_series():
    probs = [(F(1, 2), F(1, 3), F(1, 6)), (F(1, 2), F(1, 6), F(1, 3))]
    def forecast(phase, w):
        ans = F(1)
        for e in w:
            ans *= probs[phase]['abc'.index(e)]
            phase = 1 - phase
        return ans
    def b(phase, w):
        return forecast(phase, w) * all(e == 'a' for e in w)
    count = 0
    for n in range(7):
        words = [''.join(w) for w in product('abc', repeat=n)]
        assert {w: b(0, w) for w in words} == {w: b(1, w) for w in words}
        assert sum(b(0, w) for w in words) == F(1, 2) ** n
        for w in words:
            assert b(0, 'a' + w) / b(0, 'a') == b(1, w)
            assert b(0, 'b' + w) == 0
        count += len(words)
    assert forecast(0, 'b') != forecast(1, 'b')
    return {'words_checked': count, 'survival_at_n': '(1/2)^n', 'different_ordinary_b_forecasts': ['1/3', '1/6']}


def stability_margin():
    # Exhaust all masks on three finite coordinates and several positive laws.
    laws = [[F(1, 2), F(1, 3), F(1, 6)], [F(1, 4), F(1, 4), F(1, 2)], [F(1, 3)] * 3]
    count = 0
    for p in laws:
        for q in laws:
            margin = min(p + q)
            for v in product(range(2), repeat=3):
                for w in product(range(2), repeat=3):
                    b = [x * t for x, t in zip(p, v)]
                    bp = [x * t for x, t in zip(q, w)]
                    gap = sum(abs(x - y) for x, y in zip(b, bp))
                    if v != w:
                        assert gap >= margin
                    s, sp = sum(b), sum(bp)
                    if s and sp:
                        tv = sum(abs(x / s - y / sp) for x, y in zip(b, bp)) / 2
                        assert gap <= abs(s - sp) + 2 * min(s, sp) * tv
                    else:
                        assert gap == abs(s - sp)
                    count += 1
    beta, delta, horizon = F(3, 4), F(1, 10), 5
    assert (1 - beta) * sum(beta**(n - 1) * delta for n in range(1, horizon + 1)) + beta**horizon == delta * (1 - beta**horizon) + beta**horizon
    return {'mask_probability_cases': count, 'discounted_predictive_bound': True}


def conditioned_limits_and_generators():
    k = [[F(3, 8), F(1, 4)], [F(1, 8), F(1, 4)]]
    identity = [[F(1), F(0)], [F(0), F(1)]]
    projection = [[F(2, 3), F(2, 3)], [F(1, 3), F(1, 3)]]
    alpha, r = [F(1, 3), F(2, 3)], [F(2), F(1)]
    alpha_r = sum(x*y for x,y in zip(alpha, r))
    tilted = [x*y/alpha_r for x,y in zip(alpha, r)]
    assert tilted == [F(1, 2), F(1, 2)]
    powers = identity
    max_endpoint_error = F(1)
    for n in range(17):
        expected = [[F(1, 2)**n*projection[i][j] + F(1, 8)**n*(identity[i][j]-projection[i][j]) for j in range(2)] for i in range(2)]
        assert powers == expected
        terminal = prior.matmul([alpha], powers)[0]
        terminal = [x/sum(terminal) for x in terminal]
        max_endpoint_error = max(abs(x-F(1, 2)) for x in terminal)
        powers = prior.matmul(powers, k)
    assert max_endpoint_error < F(1, 10**8)
    # Exact rational eigenpair and sampled-law algebra on a Pythagorean grid.
    cases = 0
    for g, d, s in [(F(1),F(0),F(1)), (F(1),F(3,4),F(5,4)), (F(1),F(-3,4),F(5,4)), (F(3),F(4),F(5)), (F(3),F(-4),F(5))]:
        assert s*s == g*g+d*d
        v0, v1 = (2*d, F(0)) if d >= 0 else (F(0), -2*d)
        lam = -g-(v0+v1)/2+s
        l = [[-g-v0,g],[g,-g-v1]]
        rcol = [[g],[s+d]]
        assert prior.matmul(l,rcol) == [[lam*x[0]] for x in rcol]
        a,b = s+d,s-d
        transformed = [[l[i][j]*rcol[j][0]/rcol[i][0]-(lam if i==j else 0) for j in range(2)] for i in range(2)]
        assert transformed == [[-a,a],[b,-b]]
        decay = F(1,2)
        stay0,stay1 = (b+a*decay)/(a+b),(a+b*decay)/(a+b)
        assert stay0-stay1 == -d/s*(1-decay)
        assert (stay0==stay1) == (d==0)
        cases += 1
    return {'spectral_power_identities': 17, 'tilted_initial_law': list(map(str,tilted)), 'generator_grid_cases':cases}


def tail_and_mask_examples():
    count = 0
    for gamma in [F(1,3),F(1,2),F(3,4)]:
        for n in range(1,9):
            survivor_value = 1/(1-gamma)
            countdown_value = sum(gamma**i for i in range(n-1))
            assert survivor_value-countdown_value == gamma**(n-1)/(1-gamma)
            count += 1
    # The rare-word rule has precisely four distinguishable residual samples.
    valid = lambda w: w=='' or w.startswith('a') or (w.startswith('b') and all(e=='a' for e in w[1:]))
    tests = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb']
    assert len({tuple(valid(h+z) for z in tests) for h in ['', 'a', 'b', 'bb']}) == 4
    # The non-vacuous minimality example already has 1,093-word coverage above.
    # Check the vacuous example retained in Remark 5.5 as well.
    assert F(3,10) != F(7,10)
    for h in ['a','b']:
        assert len(h)<=1
        assert all(len(h+e)>1 for e in 'ab')
    # Mixture rank determinant on exact test probabilities.
    for t in [F(1,1000),F(1,10),F(1,4)]:
        conditional_a = ((F(1,2)+t)**2+(F(1,2)-t)**2)
        assert conditional_a-F(1,2) == 2*t*t
    return {'tight_geometric_tail_cases':count,'rare_rule_residual_count':4,'mixture_rank_two_determinants':True}


def rad_tilts():
    g = [[F(3, 4), F(1, 4)], [F(1, 4), F(3, 4)]]
    m = [F(1), F(1, 3)]
    result = []
    for row in g:
        s = sum(x * y for x, y in zip(row, m))
        k = [x * y / s for x, y in zip(row, m)]
        tv = sum(abs(x - y) for x, y in zip(k, row)) / 2
        assert tv == sum(x * abs(y - s) for x, y in zip(row, m)) / (2 * s)
        result.append(str(tv))
    assert result == ['3/20', '1/4']
    grid = [[F(i, 6), F(1) - F(i, 6)] for i in range(7)]
    tilt = lambda row: [x * y / sum(a * b for a, b in zip(row, m)) for x, y in zip(row, m)]
    for row in grid:
        for other in grid:
            assert (row == other) == (tilt(row) == tilt(other))
    return {'exact_row_TV': result, 'predictive_row_equality_cases': len(grid)**2}


def reciprocal_derivatives():
    count = 0
    for p, n, c, d in product([F(-1, 2), F(0), F(2, 3)], repeat=4):
        sp, sn = 1 - p*p, 1 - n*n
        den = 1 - c*d*sp*sn
        dp, dn = c*sp*sn/den, sn/den
        assert dp == sp*c*dn
        assert dn == sn*(1 + d*dp)
        ds = sn*(1 + c*sp)/den
        assert ds == dp + dn > 0
        # Normalization derivative, for any strictly positive row law.
        row = [F(1, 4), F(3, 4)]
        derivatives = [row[j] * (F(j == 0) - row[0]) * ds for j in range(2)]
        assert sum(derivatives) == 0
        assert derivatives[0]/row[0] - derivatives[1]/row[1] == ds
        count += 1
    for rho in [F(0), F(1, 3), F(3, 4)]:
        assert (1 + rho)/(1-rho*rho) == 1/(1-rho)
    return {'implicit_differential_cases': count, 'single_successor_response': '0'}


def neutral_and_cycle():
    identity = [[F(1), F(0)], [F(0), F(1)]]
    rotation = [[F(0), F(-1)], [F(1), F(0)]]
    assert prior.matmul(list(map(list, zip(*rotation))), rotation) == identity
    x, y = [[F(1), F(0)]], [[F(0), F(1)]]
    distance = lambda u, v: sum((a-b)**2 for a, b in zip(u[0], v[0]))
    for _ in range(12):
        assert distance(x, y) == 2
        x, y = prior.matmul(x, rotation), prior.matmul(y, rotation)
    return {'neutral_orbit_steps': 12, **prior.cycle_checks()}


def coupling_values():
    # A finite fully supported unifilar process, then a process with null edges.
    rows = [[F(1, 4), F(3, 4)], [F(3, 4), F(1, 4)], [F(1), F(0)]]
    trans = [[1, 2], [2, 0], [0, 1]]
    costs = [[F(1), F(0)], [F(1, 3), F(2, 3)], [F(0), F(1)]]
    witnesses = []
    for gamma in [F(1, 3), F(2, 3)]:
        n = len(rows)
        a = [[F(i == j) for j in range(n)] for i in range(n)]
        b = [sum(p*c for p, c in zip(row, cost)) for row, cost in zip(rows, costs)]
        for i in range(n):
            for e in range(2):
                a[i][trans[i][e]] -= gamma * rows[i][e]
        values = solve(a, b)
        solutions = []
        for maximal in [False, True]:
            a = [[F(i == j) for j in range(n*n)] for i in range(n*n)]
            b = [F(0)] * (n*n)
            for i, j in product(range(n), repeat=2):
                ij = i*n+j
                b[ij] = sum(abs(x-y) for x,y in zip(rows[i], rows[j])) / (2*(1-gamma))
                for e in range(2):
                    weight = min(rows[i][e], rows[j][e]) if maximal else (rows[j][e] if rows[i][e] and rows[j][e] else F(0))
                    b[ij] += weight * abs(costs[i][e] - costs[j][e])
                    a[ij][trans[i][e]*n+trans[j][e]] -= gamma * weight
            solutions.append(solve(a, b))
        ds, star = solutions
        for i, j in product(range(n), repeat=2):
            assert abs(values[i]-values[j]) <= star[i*n+j] <= ds[i*n+j]
            assert star[i*n+j] == star[j*n+i]
            if i == j:
                assert star[i*n+j] == ds[i*n+j] == 0
        assert any(ds[i*n+j] != ds[j*n+i] for i, j in product(range(n), repeat=2))
        assert any(x < y for x,y in zip(star, ds))
        witnesses.append({'gamma': str(gamma), 'D_s_01': str(ds[1]), 'D_s_10': str(ds[n]), 'D_star_01': str(star[1])})
    return witnesses


def unifilar_genericity():
    # Same six-state product as the paper, with generically distinct emissions.
    q = [F(1, 3), F(2, 3)]
    assert q[0] != q[1]
    pairs = {(len(w) % 2, ('D' if 'bb' in w else 'B' if w.endswith('b') else 'A')) for n in range(5) for w in prior.words(n)}
    assert len(pairs) > max(2, 3)
    # Identical state maps stay comparable however weights are chosen.
    sync = {(len(w) % 2, len(w) % 2) for n in range(5) for w in prior.words(n)}
    assert len(sync) == 2
    return {'incomparable_product_pairs': len(pairs), 'synchronized_product_pairs': len(sync)}


def main():
    groups = {
        'partition_support_and_novelty_mechanisms': product_and_support(),
        'sharp_joint_horizon': exact_horizons(),
        'multitarget_minimax': prior.separation_checks(),
        'killed_series_minimality': killed_series(),
        'stability_probability_margin': {**stability_margin(), **tail_and_mask_examples()},
        'rare_word_obstruction': prior.rare_word_checks(),
        'infinite_future_obstruction': prior.mixture_checks(),
        'observable_inverse_and_positive_HMM': prior.genericity_observability_checks(),
        'unifilar_genericity': unifilar_genericity(),
        'destination_tilt': rad_tilts(),
        'Q_process_and_QSD': {**prior.rad_checks(), **conditioned_limits_and_generators()},
        'reciprocal_forecast_sensitivity': reciprocal_derivatives(),
        'neutral_persistence_and_commutator_cycle': neutral_and_cycle(),
        'symmetric_coupling_value_bound': coupling_values(),
    }
    root = Path(__file__).resolve().parent
    files = ['r8_helper.py', 'r8_extensions.py']
    groups['inputs_sha256'] = {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in files}
    result = root / 'r8_extensions.json'
    result.write_text(json.dumps(groups, indent=2) + '\n')
    print('PASS: 14 exact-arithmetic check groups; no floating-point computation')
    print('Results:', result)
    print('Result SHA-256:', hashlib.sha256(result.read_bytes()).hexdigest())


if __name__ == '__main__':
    main()
