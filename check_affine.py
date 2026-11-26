"""Independent finite checks for the affine-hull argument. Run with Python 3.10+."""
from itertools import combinations
from random import Random


def parity(x):
    return x.bit_count() % 2


def rref(rows, width):
    rows = list(rows)
    rank = 0
    for bit in range(width):
        pivot = next((j for j in range(rank, len(rows)) if rows[j] >> bit & 1), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for j in range(len(rows)):
            if j != rank and rows[j] >> bit & 1:
                rows[j] ^= rows[rank]
        rank += 1
    return rows[:rank]


def all_sat_sets(m):
    """OR over certificates for each rank/bit query, then compare to parity equations."""
    width = m + 1
    npoints = 1 << m
    nsets = 1 << npoints
    # A block per rank: a presence bit then the bits of the padded RREF.
    stride = 1 + width * width
    answers = [0] * nsets
    for rank in range(1, width + 1):
        for points in combinations(range(npoints), rank):
            rows = rref((x | npoints for x in points), width)
            if len(rows) == rank:
                packed = sum(row << (i * width) for i, row in enumerate(rows))
                answers[sum(1 << x for x in points)] = (1 | packed << 1) << (rank * stride)
    # Subset zeta transform for bitwise OR. Each bit now records existence of
    # an independent subcollection with that output bit among the given models.
    for i in range(npoints):
        bit = 1 << i
        for s in range(nsets):
            if s & bit:
                answers[s] |= answers[s ^ bit]

    hyperplanes = []
    for z in range(npoints):
        odd = sum(1 << x for x in range(npoints) if parity(z & x))
        hyperplanes.extend((odd, nsets - 1 - odd))
    for s, output in enumerate(answers):
        actual = nsets - 1
        for h in hyperplanes:
            if not s & ~h:
                actual &= h
        if not output:
            assert not s and not actual
            continue
        rank = (output.bit_length() - 1) // stride
        block = (output >> (rank * stride)) >> 1
        basis = [(block >> (i * width)) & ((1 << width) - 1) for i in range(rank)]
        vectors = {0}
        for row in basis:
            vectors |= {v ^ row for v in vectors}
        slice_mask = sum(1 << (v ^ npoints) for v in vectors if v & npoints)
        assert slice_mask == actual, (m, s, basis)
    return nsets


def completions(basis, m, prefix, k):
    """Solutions to V z = 0 given the first k bits, by augmented elimination."""
    free = m - k
    rhs = 1 << free
    reduced = rref(((row >> k) | parity(row & prefix) * rhs for row in basis), free + 1)
    return 0 if rhs in reduced else 1 << (free - len(reduced))


def splitter(bases, m):
    prefix = 0
    for k in range(m):
        choices = [prefix, prefix | (1 << k)]
        costs = [sum(completions(b, m, v, k + 1) for b in bases) for v in choices]
        prefix = choices[costs[1] < costs[0]]
    return prefix


def families():
    # Compare prefix counts to brute force, including inconsistent systems.
    rng = Random(67102)
    number = 0
    splits = 0
    for m in range(1, 10):
        for _ in range(100):
            k = rng.randrange(m + 1)
            prefix = rng.randrange(1 << k)
            bases = [rref((rng.randrange(1 << m) for _ in range(rng.randrange(m + 1))), m)
                     for _ in range(rng.randint(1, 7))]
            for basis in bases:
                ref = sum(all(not parity(row & v) for row in basis)
                          for v in range(prefix, 1 << m, 1 << k))
                assert completions(basis, m, prefix, k) == ref
                number += 1
            if sum(1 << (m - len(b)) for b in bases) < (1 << m):
                z = splitter(bases, m)
                assert all(any(parity(z & v) for v in b) for b in bases)
                splits += 1
    return number, splits


def search_trials():
    """Run repeated restrictions with decoy hulls. Explicit models supply the list promise."""
    rng = Random(15988)
    trials = 0
    cut_count = 0
    max_cuts = 0
    for m in range(4, 10):
        size = 1 << m
        for trial in range(120):
            original = {x for x in range(size) if rng.randrange(2 + trial % 23) == 0}
            if trial % 9 == 0:
                original.clear()
            models = original.copy()
            cuts = 0
            answer = None
            for round_index in range(m + 1):
                candidates = []
                for _ in range(rng.randrange(7)):
                    # Mix large decoys, singletons, and translated proper subspaces.
                    rows = [rng.randrange(size) for _ in range(rng.randint(0, m))]
                    candidates.append((rng.randrange(size), rref(rows, m)))
                if models:
                    a = min(models)
                    candidates.insert(rng.randrange(len(candidates) + 1),
                                      (a, rref((a ^ x for x in models), m)))
                # ceil(log2(K+1)) equals the bit length of K, including K=0.
                threshold = len(candidates).bit_length()
                large = []
                for a, basis in candidates:
                    if len(basis) > threshold:
                        large.append(basis)
                        continue
                    points = {a}
                    for v in basis:
                        points |= {x ^ v for x in points}
                    hits = points & models
                    if hits:
                        answer = min(hits)
                        break
                if answer is not None or not large or round_index == m:
                    break
                z = splitter(large, m)
                remaining = {x for x in models if not parity(x & z)}
                if models:
                    assert remaining and remaining != models
                    anchor = min(remaining)
                    old_dim = len(rref((anchor ^ x for x in models), m))
                    new_dim = len(rref((anchor ^ x for x in remaining), m))
                    assert new_dim < old_dim
                models = remaining
                cuts += 1
            assert (answer in original) == bool(original)
            trials += 1
            cut_count += cuts
            max_cuts = max(max_cuts, cuts)
    return trials, cut_count, max_cuts


if __name__ == "__main__":
    print("All SAT sets checked, by dimension:", [all_sat_sets(m) for m in range(5)])
    counts, splits = families()
    print("Prefix counts checked:", counts, "simultaneous splitters checked:", splits)
    print("Search trials, total cuts, maximum cuts in a trial:", search_trials())
