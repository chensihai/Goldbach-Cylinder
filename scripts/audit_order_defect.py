#!/usr/bin/env python3
"""Exact CRT audit of the two-base Lucas ordinary-order defect.

The enumeration cost is O(J), where J is the number of admissible CRT pairs,
instead of O(M^2).  All counts and displayed ratios are exact integers or
reduced rational numbers.
"""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
from pathlib import Path

import numpy as np


def lucas_pairs(base: int, depth: int) -> tuple[np.ndarray, np.ndarray]:
    """Return every `(n,k) < base^depth` with digitwise `k_i <= n_i`."""
    ns = np.array([0], dtype=np.int64)
    ks = np.array([0], dtype=np.int64)
    place = 1
    for _ in range(depth):
        digit_pairs = [(n, k) for n in range(base) for k in range(n + 1)]
        ns = np.concatenate([ns + n * place for n, _ in digit_pairs])
        ks = np.concatenate([ks + k * place for _, k in digit_pairs])
        place *= base
    return ns, ks


def crt_lift(a: np.ndarray, b: np.ndarray, pmod: int, qmod: int) -> np.ndarray:
    """Canonical representative modulo `pmod*qmod` with residues `a,b`."""
    inverse = pow(pmod, -1, qmod)
    return a + pmod * (((b - a) * inverse) % qmod)


def exact_counts(p: int, q: int, r: int, s: int, chunk: int) -> dict[str, int]:
    pmod, qmod = p**r, q**s
    pn, pk = lucas_pairs(p, r)
    qn, qk = lucas_pairs(q, s)
    h = 0
    ht = 0
    for start in range(0, len(pn), chunk):
        n = crt_lift(pn[start : start + chunk, None], qn[None, :], pmod, qmod)
        k = crt_lift(pk[start : start + chunk, None], qk[None, :], pmod, qmod)
        h += int(np.count_nonzero(k <= n))
        ht += int(np.count_nonzero(n <= k))
    m = pmod * qmod
    j = len(pn) * len(qn)
    defect = h - ht
    assert h + ht == j + m
    assert 2 * h == j + m + defect
    return {"p": p, "q": q, "r": r, "s": s, "M": m, "J": j,
            "H": h, "Ht": ht, "A": defect}


def frac(n: int, d: int) -> str:
    return str(Fraction(n, d)) if d else "undefined"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("audit/order_defect.csv"))
    parser.add_argument("--chunk", type=int, default=128)
    args = parser.parse_args()

    rows = [
        exact_counts(p, q, r, s, args.chunk)
        for p, q in [(3, 5), (3, 7), (5, 7)]
        for r in range(1, 4)
        for s in range(1, 4)
    ]
    lookup = {(x["p"], x["q"], x["r"], x["s"]): x for x in rows}

    fields = ["p", "q", "r", "s", "M", "J", "H", "Ht", "A",
              "A_over_J_minus_M", "A_over_J", "A_over_M", "H_over_J",
              "R_p", "R_q", "exchange_delta"]
    output_rows = []
    for x in rows:
        p, q, r, s = x["p"], x["q"], x["r"], x["s"]
        y = dict(x)
        y["A_over_J_minus_M"] = frac(x["A"], x["J"] - x["M"])
        y["A_over_J"] = frac(x["A"], x["J"])
        y["A_over_M"] = frac(x["A"], x["M"])
        y["H_over_J"] = frac(x["H"], x["J"])
        y["R_p"] = frac(lookup[(p, q, r + 1, s)]["A"], x["A"]) if r < 3 else ""
        y["R_q"] = frac(lookup[(p, q, r, s + 1)]["A"], x["A"]) if s < 3 else ""
        swapped = exact_counts(q, p, s, r, args.chunk)
        y["exchange_delta"] = x["A"] - swapped["A"]
        output_rows.append(y)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(output_rows)

    for y in output_rows:
        print(",".join(str(y[field]) for field in fields))


if __name__ == "__main__":
    main()
