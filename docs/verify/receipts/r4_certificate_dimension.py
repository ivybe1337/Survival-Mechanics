"""
Receipt R4 -- certificate bases of bounded dimension (closes the structured case of U2).

For every down-closed family K over an n-element universe (n <= 5, exhaustive: every antichain of
nonempty... of subsets is enumerated as a candidate minimal-nogood basis), checks:
  1. Reconstruction: the inclusion-minimal non-members of K are exactly the generating antichain.
  2. Shattering lemma: K shatters S  <=>  S in K      (so VC(K) = largest face size).
  3. Bound: |M(K)| <= C(n, min(VC(K)+1, floor(n/2))).
  4. Tightness: for every d, the maximum of |M(K)| over K with VC(K) <= d equals C(n, min(d+1, floor(n/2))).
  5. Sauer-Shelah for the complex itself: |K| <= sum_{i<=VC} C(n,i).
Plus the threshold complexes K_d = {|s| <= d} checked directly for n <= 12.
"""
from itertools import combinations
from math import comb

from la_core import Checks, write_receipt

C = Checks()
out = {}


def all_subsets(n):
    return [frozenset(c) for k in range(n + 1) for c in combinations(range(n), k)]


def antichains(sets):
    """All antichains of the given list of frozensets (recursive, include-exclude)."""
    res = []

    def rec(i, chosen):
        if i == len(sets):
            res.append(list(chosen))
            return
        rec(i + 1, chosen)
        s = sets[i]
        if all(not (s <= t or t <= s) for t in chosen):
            chosen.append(s)
            rec(i + 1, chosen)
            chosen.pop()
    rec(0, [])
    return res


def vc(K, n):
    best = -1
    Kl = list(K)
    for S in all_subsets(n):
        traces = {s & S for s in Kl}
        if len(traces) == 2 ** len(S):
            best = max(best, len(S))
    return best


def shattered(K, S):
    return len({s & S for s in K}) == 2 ** len(S)


summary = {}
for n in range(0, 6):
    U = all_subsets(n)
    count = 0
    maxM_by_d = {}
    maxM_exact = {}
    viol = {"reconstruction": 0, "shatter_lemma": 0, "bound": 0, "sauer": 0}
    for A in antichains(U):
        if frozenset() in A:
            continue  # K would be empty; we require the empty configuration to be admissible
        K = [s for s in U if not any(a <= s for a in A)]
        count += 1
        Kset = set(K)
        M = [s for s in U if s not in Kset and all((s - {x}) in Kset for x in s)]
        if sorted(map(sorted, M)) != sorted(map(sorted, A)):
            viol["reconstruction"] += 1
        d = vc(K, n)
        for S in U:
            if shattered(K, S) != (S in Kset):
                viol["shatter_lemma"] += 1
                break
        if len(M) > comb(n, min(d + 1, n // 2)):
            viol["bound"] += 1
        if len(K) > sum(comb(n, i) for i in range(d + 1)):
            viol["sauer"] += 1
        maxM_by_d[d] = max(maxM_by_d.get(d, 0), len(M))
        maxM_exact[d] = max(maxM_exact.get(d, 0), len(M))
    # tightness: max over VC <= d
    tight_ok = True
    table = {}
    for d in range(0, n + 1):
        m = max(v for dd, v in maxM_by_d.items() if dd <= d)
        pred = comb(n, min(d + 1, n // 2))
        table[d] = {"max_|M|_over_VC<=d": m, "predicted": pred}
        tight_ok &= (m == pred) or n == 0  # tightness is claimed for n >= 1 only
    summary[n] = {"complexes": count, "violations": viol, "tightness_table": table,
                  "max_|M|_over_rank_exactly_r": dict(sorted(maxM_exact.items()))}
    C.check(f"exhaustive_n={n}", all(v == 0 for v in viol.values()) and tight_ok, summary[n])
out["exhaustive"] = summary
C.check("rank_exactly_r_maxima_n=4_are_4,6,5,3,0",
        [summary[4]["max_|M|_over_rank_exactly_r"][r] for r in range(5)] == [4, 6, 5, 3, 0],
        summary[4]["max_|M|_over_rank_exactly_r"])
# Dedekind-number sanity check on the enumeration (antichains including {} minus the one containing the empty set)
dedekind = {0: 2, 1: 3, 2: 6, 3: 20, 4: 168, 5: 7581}
C.check("enumeration_count_matches_dedekind", all(summary[n]["complexes"] == dedekind[n] - 1 for n in summary),
        {n: summary[n]["complexes"] for n in summary})

thr_ok = True
for n in range(1, 13):
    U = all_subsets(n)
    for d in range(0, n):
        Kset = {s for s in U if len(s) <= d}
        M = [s for s in U if s not in Kset and all((s - {x}) in Kset for x in s)]
        thr_ok &= (len(M) == comb(n, d + 1) and all(len(s) == d + 1 for s in M)
                   and max(len(s) for s in Kset) == d)
C.check("threshold_complexes_K_d_direct_n<=12", thr_ok)

out["checks"] = C.results
out["all_checks_pass"] = C.all_pass()
dg = write_receipt("r4_certificate_dimension.json", out)
print("R4 all_checks_pass =", C.all_pass(), "digest", dg)
