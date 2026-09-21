#!/usr/bin/env python3
"""Audit the exact anchored CRT transfer and its translation quotient."""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from audit_order_defect import lucas_pairs
from audit_phase_transfer import common_shift_defects, phase_buckets


def anchored_histogram(p: int, q: int, r: int, s: int):
    pmod, qmod = p**r, q**s
    pn, pk = lucas_pairs(p, r)
    qn, qk = lucas_pairs(q, s)
    inverse = pow(pmod, -1, qmod)
    mass = np.zeros((qmod, qmod), dtype=np.int64)
    signed = np.zeros_like(mass)
    for i in range(len(pn)):
        cn = ((qn - pn[i]) * inverse) % qmod
        ck = ((qk - pk[i]) * inverse) % qmod
        n = pn[i] + pmod * cn
        k = pk[i] + pmod * ck
        np.add.at(mass, (ck, cn), 1)
        np.add.at(signed, (ck, cn), (k < n).astype(np.int64) - (k > n).astype(np.int64))
    return mass, signed


def anchored_transfer(p: int, qmod: int, old: np.ndarray) -> np.ndarray:
    result = np.zeros_like(old)
    inverse = pow(p, -1, qmod)
    for ck in range(qmod):
        for cn in range(qmod):
            value = int(old[ck, cn])
            for a in range(p):
                for b in range(a + 1):
                    result[(inverse * (ck - b)) % qmod,
                           (inverse * (cn - a)) % qmod] += value
    return result


def phase_projection(anchored: np.ndarray) -> np.ndarray:
    qmod = anchored.shape[0]
    return np.array([
        sum(int(anchored[c, (c + h) % qmod]) for c in range(qmod))
        for h in range(qmod)
    ], dtype=np.int64)


def audit(case: tuple[int, int, int, int]) -> dict[str, object]:
    p, q, r, s = case
    qmod = q**s
    mass, signed = anchored_histogram(*case)
    next_mass, _ = anchored_histogram(p, q, r + 1, s)
    projected = phase_projection(mass)
    plus, minus, zero = phase_buckets(*case)
    phase = plus + minus + zero
    shift_sum = sum(common_shift_defects(*case))
    phase_formula = int(qmod * int(plus[0] - minus[0]) + sum(
        (qmod - 2 * h) * int(phase[h]) for h in range(1, qmod)))
    mass_fft = np.fft.fft2(mass)
    signed_fft = np.fft.fft2(signed)
    tolerance = 1e-8
    phase_modes = [(x, (-x) % qmod) for x in range(qmod)]
    phase_mass_active = int(sum(abs(mass_fft[x, y]) > tolerance for x, y in phase_modes))
    phase_signed_active = int(sum(abs(signed_fft[x, y]) > tolerance for x, y in phase_modes))
    return {
        "p": p, "q": q, "r": r, "s": s, "Q": qmod,
        "anchored_transfer_exact": bool(np.array_equal(anchored_transfer(p, qmod, mass), next_mass)),
        "phase_projection_exact": bool(np.array_equal(projected, phase)),
        "shift_sum": int(shift_sum),
        "shift_sum_phase_formula": phase_formula,
        "shift_sum_formula_exact": shift_sum == phase_formula,
        "active_mass_fourier_modes": int(np.count_nonzero(abs(mass_fft) > tolerance)),
        "active_mass_phase_modes": phase_mass_active,
        "active_signed_fourier_modes": int(np.count_nonzero(abs(signed_fft) > tolerance)),
        "active_signed_phase_modes": phase_signed_active,
    }


def main() -> None:
    cases = [(3, 5, 1, 1), (3, 5, 1, 2), (3, 7, 1, 1), (5, 7, 1, 1)]
    result = [audit(case) for case in cases]
    output = Path("audit/anchored_transfer.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
