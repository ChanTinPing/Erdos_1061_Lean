from __future__ import annotations

import argparse
import math
from fractions import Fraction
from functools import lru_cache
from time import monotonic


def smallest_factors(bound: int) -> list[int]:
    result = list(range(bound + 1))
    for prime in range(2, math.isqrt(bound) + 1):
        if result[prime] == prime:
            for n in range(prime * prime, bound + 1, prime):
                if result[n] == n:
                    result[n] = prime
    return result


def factor(n: int, sf: list[int]) -> list[tuple[int, int]]:
    factors = []
    while n > 1:
        p, e = sf[n], 0
        while n % p == 0:
            n //= p
            e += 1
        factors.append((p, e))
    return factors


@lru_cache(maxsize=None)
def local_ray_values(p: int, e: int, exponent: int) -> list[tuple[Fraction, int]]:
    return [(Fraction(p ** (t + e + 1) - 1, p**e * (p ** (t + 1) - 1)), p**t) for t in range(exponent + 1)]



def run(bound: int, exponent: int) -> None:
    start = monotonic()
    spf = smallest_factors(bound)
    # Retain singleton groups in compact tuple form to avoid a dict per ray value.
    seen = {}
    count, pair_count, triple_count = 0, 0, 0
    for w in range(2, bound + 1):
        values = [(Fraction(1), 1)]
        for p, e in factor(w, spf):
            values = [
                (old_value * value, old_mult * mult)
                for old_value, old_mult in values
                for value, mult in local_ray_values(p, e, exponent)
            ]
        for value, mw in dict(values).items():
            count += 1
            group = seen.get(value)
            if group is None:
                seen[value] = (w, mw)
                continue
            if isinstance(group, tuple):
                group = dict([group])
                seen[value] = group
            pair_count += len(group)
            for u, mu in group.items():
                v = w - u
                if v <= u or v not in group or math.gcd(u, v) != 1:
                    continue
                mv = group[v]
                g = mu * mv * mw
                a, b, c = g * u, g * v, g * w
                # Compute the sigma ratios directly from the known normalized prime factor supports.
                for j, base_mult in [(u, mu), (v, mv), (w, mw)]:
                    ratio = Fraction(1)
                    for p, e in factor(j, spf):
                        t = 0
                        while base_mult % p == 0:
                            base_mult //= p
                            t += 1
                        ratio *= Fraction(p ** (t + e + 1) - 1, p**e * (p ** (t + 1) - 1))
                    assert ratio == value
                print(f'additive friendly triple {a}+{b}={c}, core {u}+{v}={w}, common multiplier {g}, ratio increase {value}', flush=True)
                triple_count += 1
            group[w] = mw
        if w % 1000 == 0:
            print(f'progress {w}: {count} values, {len(seen)} distinct, {pair_count} matches, {triple_count} triples, {(monotonic()-start):.2f}s', flush=True)
    print(f'done {bound}: {count} values, {len(seen)} distinct, {pair_count} matches, {triple_count} triples, {(monotonic()-start):.2f}s', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--bound', type=int, default=10000)
    parser.add_argument('--exponent', type=int, default=4)
    arguments = parser.parse_args()
    run(arguments.bound, arguments.exponent)
