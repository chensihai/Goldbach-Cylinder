# Anchored CRT transfer audit

The audit confirms three exact finite identities.

1. The histogram on `(c_k,c_n)` obeys the deterministic digit transition
   ```text
   (c_k,c_n) -> (p^{-1}(c_k-b), p^{-1}(c_n-a)),  0 <= b <= a < p.
   ```
2. Summing the anchored histogram along translation orbits,
   `sum_c N(c,c+h)`, is exactly the earlier phase histogram.
3. If `N_h` is phase mass and `A_0` is the signed contribution at phase zero,
   the sum of defects over all common q-coordinate shifts is
   ```text
   Q*A_0 + sum_{h=1}^{Q-1} (Q-2h)*N_h.
   ```

All three identities pass for `(3,5;1,1)`, `(3,5;1,2)`, `(3,7;1,1)`, and
`(5,7;1,1)`.  The last formula exactly reproduces the previously observed
shift sums.

The numerical two-dimensional DFT reconnaissance in `anchored_transfer.json`
also records active modes.  It is diagnostic only: exact vanishing should be
proved algebraically before it is used.  Both the common-translation invariant
sector `xi+eta=0` and its complement are active in the sampled distributions.

The anchored state is therefore a closed finite dynamical system, while its
translation quotient is precisely the phase marginal.  The order observable
on the quotient is a sawtooth kernel `Q-2h`, plus the phase-zero local strict
term.  These exact identities are suitable candidates for the next Lean layer;
no spectral-decay claim is made here.
