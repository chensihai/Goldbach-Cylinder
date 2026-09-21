# Exact two-base order-defect audit

This is discovery data, not a theorem about positivity or decay.  The complete
machine-readable table is in `order_defect.csv` and can be regenerated with:

```text
python3 scripts/audit_order_defect.py
```

The enumeration visits the `J` admissible CRT pairs directly.  It does not scan
the full square of `M^2` pairs.  Three low-cost cases were independently checked
against a direct `M^2` enumeration.

## Signed defect matrices

Rows are `r = 1,2,3`; columns are `s = 1,2,3`.

```text
(p,q) = (3,5)
      27       423      6519
      99       951     12303
     657      4113     36321

(p,q) = (3,7)
      51      1473     42987
     213      3591     91089
     963      9009    188619

(p,q) = (5,7)
      97      2311     65245
     977      8231    245585
   12841     56767    934357
```

Every sampled defect is positive.  This is only a finite observation.

## Main observations

- The exact checks `H + Ht = J + M` and `2H = J + M + A` pass in every case.
- Swapping `(p,r)` with `(q,s)` gives `exchange_delta = 0` in every case.  This
  points to a definition-level exchange invariance worth proving next.
- `A/(J-M)` generally becomes smaller at larger joint depth, but it is not
  monotone on the `3 x 3` grids.  For `(r,s)=(3,3)` it equals
  `12107/241875`, `62873/1577457`, and `934357/74045125` for `(3,5)`, `(3,7)`,
  and `(5,7)` respectively.
- The exact depth ratios in the CSV vary strongly with the other depth.  The
  present data does not support a constant one-dimensional recurrence ratio.
- The largest case, `(5,7;3,3)`, has `M=42875`, `J=74088000`,
  `H=37532616`, `Ht=36598259`, and `A=934357`.

The next formal target suggested by the data is exchange invariance of the
canonical integer CRT relation.  Transfer or spectral claims need more depths
or a structural recurrence before formalization.
