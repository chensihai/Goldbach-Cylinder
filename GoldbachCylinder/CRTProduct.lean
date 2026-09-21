import Mathlib

/-!
# Exact product count under the Chinese remainder equivalence

The construction lifts arbitrary local pair finsets through the two-coordinate
CRT equivalence.  Its cardinality is exactly the product of the local cards.
-/

namespace GoldbachCylinder

noncomputable section

/-- CRT applied simultaneously to both coordinates of a residue pair. -/
def crtPairEquiv {P Q : ℕ} (hPQ : P.Coprime Q) :
    (ZMod (P * Q) × ZMod (P * Q)) ≃
      ((ZMod P × ZMod P) × (ZMod Q × ZMod Q)) where
  toFun x :=
    let e := (ZMod.chineseRemainder hPQ).toEquiv
    (((e x.1).1, (e x.2).1), ((e x.1).2, (e x.2).2))
  invFun x :=
    let e := (ZMod.chineseRemainder hPQ).toEquiv
    (e.symm (x.1.1, x.2.1), e.symm (x.1.2, x.2.2))
  left_inv x := by
    simp
  right_inv x := by
    simp

/-- The simultaneous CRT lift of two local admissible pair finsets. -/
def crtPairLift {P Q : ℕ} (hPQ : P.Coprime Q)
    (A : Finset (ZMod P × ZMod P))
    (B : Finset (ZMod Q × ZMod Q)) :
    Finset (ZMod (P * Q) × ZMod (P * Q)) :=
  (A.product B).map (crtPairEquiv hPQ).symm.toEmbedding

/-- Exact independence on a complete CRT residue box. -/
theorem card_crtPairLift {P Q : ℕ} (hPQ : P.Coprime Q)
    (A : Finset (ZMod P × ZMod P))
    (B : Finset (ZMod Q × ZMod Q)) :
    (crtPairLift hPQ A B).card = A.card * B.card := by
  simp [crtPairLift]

theorem coprime_primePow_primePow
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.Coprime (p ^ r) (q ^ s) := by
  have hpq_coprime : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr (by
    intro hdvd
    exact hpq ((hq.dvd_iff_eq hp.ne_one).mp hdvd).symm)
  exact hpq_coprime.pow r s

end

end GoldbachCylinder
