#!/usr/bin/env python3
"""Exact discovery audit for CRT phase and wrap transfer states."""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path

import numpy as np

from audit_order_defect import crt_lift, lucas_pairs


def phase_buckets(p: int, q: int, r: int, s: int):
    pmod, qmod = p**r, q**s
    pn, pk = lucas_pairs(p, r)
    qn, qk = lucas_pairs(q, s)
    inverse = pow(pmod, -1, qmod)
    plus = np.zeros(qmod, dtype=np.int64)
    minus = np.zeros(qmod, dtype=np.int64)
    zero = np.zeros(qmod, dtype=np.int64)
    for i in range(len(pn)):
        cn = ((qn - pn[i]) * inverse) % qmod
        ck = ((qk - pk[i]) * inverse) % qmod
        phase = (cn - ck) % qmod
        n = pn[i] + pmod * cn
        k = pk[i] + pmod * ck
        np.add.at(plus, phase, k < n)
        np.add.at(minus, phase, k > n)
        np.add.at(zero, phase, k == n)
    return plus, minus, zero


def phase_histogram(p: int, q: int, r: int, s: int) -> np.ndarray:
    buckets = phase_buckets(p, q, r, s)
    return sum(buckets)


def verify_phase_transfer(p: int, q: int, r: int, s: int) -> bool:
    qmod = q**s
    old = phase_histogram(p, q, r, s)
    new = phase_histogram(p, q, r + 1, s)
    predicted = np.zeros(qmod, dtype=np.int64)
    inverse = pow(p, -1, qmod)
    for phase, mass in enumerate(old):
        for difference in range(p):
            predicted[(inverse * (phase - difference)) % qmod] += (p - difference) * mass
    return bool(np.array_equal(new, predicted))


def nonclosed_wrap_transitions(p: int, q: int, r: int, s: int) -> tuple[int, int]:
    """Count `(h,wrap,a,b)` keys with more than one possible successor wrap."""
    pmod, qmod = p**r, q**s
    pn, pk = lucas_pairs(p, r)
    qn, qk = lucas_pairs(q, s)
    inverse = pow(pmod, -1, qmod)
    next_inverse = pow(p * pmod, -1, qmod)
    transitions: dict[tuple[int, int, int, int], set[tuple[int, int]]] = defaultdict(set)
    for i in range(len(pn)):
        cn = ((qn - pn[i]) * inverse) % qmod
        ck = ((qk - pk[i]) * inverse) % qmod
        for j in range(len(qn)):
            phase = int((cn[j] - ck[j]) % qmod)
            wrap = int(cn[j] < ck[j])
            for a in range(p):
                for b in range(a + 1):
                    cn2 = int(((qn[j] - (pn[i] + a * pmod)) * next_inverse) % qmod)
                    ck2 = int(((qk[j] - (pk[i] + b * pmod)) * next_inverse) % qmod)
                    transitions[(phase, wrap, a, b)].add(
                        ((cn2 - ck2) % qmod, int(cn2 < ck2)))
    bad = sum(len(successors) > 1 for successors in transitions.values())
    return len(transitions), bad


def common_shift_defects(p: int, q: int, r: int, s: int) -> list[int]:
    """Shift both q-coordinates by `u`, retaining the unshifted local relation."""
    pmod, qmod = p**r, q**s
    pn, pk = lucas_pairs(p, r)
    qn, qk = lucas_pairs(q, s)
    defects = []
    for shift in range(qmod):
        defect = 0
        for i in range(len(pn)):
            n = crt_lift(pn[i], (qn + shift) % qmod, pmod, qmod)
            k = crt_lift(pk[i], (qk + shift) % qmod, pmod, qmod)
            defect += int(np.count_nonzero(k < n)) - int(np.count_nonzero(k > n))
        defects.append(defect)
    return defects


def audit_case(case: tuple[int, int, int, int]) -> dict[str, object]:
    p, q, r, s = case
    plus, minus, zero = phase_buckets(*case)
    total_keys, bad_keys = nonclosed_wrap_transitions(*case)
    shifts = common_shift_defects(*case)
    return {
        "p": p, "q": q, "r": r, "s": s, "Q": q**s,
        "occupied_phases": int(np.count_nonzero(plus + minus + zero)),
        "mixed_sign_phases": int(np.count_nonzero((plus > 0) & (minus > 0))),
        "phase_transfer_exact": verify_phase_transfer(*case),
        "wrap_transition_keys": total_keys,
        "nonclosed_wrap_transition_keys": bad_keys,
        "defect": int((plus - minus).sum()),
        "common_shift_sum": sum(shifts),
        "common_shift_min": min(shifts),
        "common_shift_max": max(shifts),
        "common_shift_defects": shifts,
    }


def main() -> None:
    cases = [(3, 5, 1, 1), (3, 5, 2, 1), (3, 7, 1, 2), (5, 7, 1, 1)]
    result = [audit_case(case) for case in cases]
    output = Path("audit/phase_transfer.json")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
