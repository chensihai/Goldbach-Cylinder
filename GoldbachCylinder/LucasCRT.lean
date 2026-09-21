import GoldbachCylinder.CRTProduct
import Cylinder_RH.LucasRowCount

/-!
# Actual Lucas residue pairs and their two-base CRT lift

The local type stores an actual Pascal entry `(n,k)` with `n < p^d`, `k ≤ n`,
and `p ∤ n.choose k`.  It is embedded into the corresponding pair of residue
classes, then lifted through the genuine `ZMod` Chinese remainder equivalence.
-/

open scoped BigOperators

namespace GoldbachCylinder

noncomputable section

/-- Actual nonzero entries in one Pascal row. -/
abbrev RowResidue (p n : ℕ) :=
  ↥((Finset.range (n + 1)).filter fun k => ¬p ∣ Nat.choose n k)

/-- An actual Pascal entry in the complete `p^d` row block that is nonzero modulo `p`. -/
abbrev PascalResidue (p d : ℕ) := Σ n : Fin (p ^ d), RowResidue p n.1

private theorem card_rowResidue (p n : ℕ) :
    Fintype.card (RowResidue p n) = CylinderRH.pascalNonzeroCount p n := by
  rw [Fintype.card_coe, CylinderRH.pascalNonzeroCount]

/-- Formula (237): exact cardinality of the complete actual Lucas residue block. -/
theorem card_pascalResidue (p d : ℕ) (hp : p.Prime) :
    Fintype.card (PascalResidue p d) = (p * (p + 1) / 2) ^ d := by
  rw [Fintype.card_sigma]
  simp_rw [card_rowResidue]
  rw [Fin.sum_univ_eq_sum_range]
  exact CylinderRH.sum_pascalNonzeroCount_range_pow p d hp

private theorem pow_ne_zero_of_prime {p d : ℕ} (hp : p.Prime) : p ^ d ≠ 0 :=
  pow_ne_zero d hp.ne_zero

private def pascalResidueFinEmbedding (p d : ℕ) :
    PascalResidue p d ↪ (Fin (p ^ d) × Fin (p ^ d)) where
  toFun x :=
    (x.1, ⟨x.2.1, lt_of_lt_of_le
      (Finset.mem_range.mp (Finset.mem_filter.mp x.2.2).1)
      (Nat.succ_le_of_lt x.1.2)⟩)
  inj' := by
    intro x y hxy
    have hn : x.1 = y.1 := congrArg Prod.fst hxy
    cases x with
    | mk xn xk =>
      cases y with
      | mk yn yk =>
        simp only at hn
        subst yn
        have hk : xk = yk := by
          apply Subtype.ext
          exact congrArg (fun z => z.1) (congrArg Prod.snd hxy)
        exact congrArg (fun k => Sigma.mk xn k) hk

/-- Embed the actual `(n,k)` pair into its two residue classes modulo `p^d`. -/
def pascalResidueEmbedding (p d : ℕ) (hp : p.Prime) :
    PascalResidue p d ↪ (ZMod (p ^ d) × ZMod (p ^ d)) := by
  letI : NeZero (p ^ d) := ⟨pow_ne_zero_of_prime hp⟩
  exact (pascalResidueFinEmbedding p d).trans
    ((ZMod.finEquiv (p ^ d)).toEquiv.prodCongr
      (ZMod.finEquiv (p ^ d)).toEquiv).toEmbedding

/-- The actual local Lucas pair finset inside the residue square modulo `p^d`. -/
def pascalResidueFinset (p d : ℕ) (hp : p.Prime) :
    Finset (ZMod (p ^ d) × ZMod (p ^ d)) :=
  Finset.univ.map (pascalResidueEmbedding p d hp)

theorem card_pascalResidueFinset (p d : ℕ) (hp : p.Prime) :
    (pascalResidueFinset p d hp).card = (p * (p + 1) / 2) ^ d := by
  rw [pascalResidueFinset, Finset.card_map, Finset.card_univ]
  exact card_pascalResidue p d hp

/-- Formula (240): exact two-base Lucas factorization on a complete CRT residue box. -/
theorem twoBaseLucasResidue_card
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (crtPairLift (coprime_primePow_primePow hp hq hpq)
      (pascalResidueFinset p r hp) (pascalResidueFinset q s hq)).card =
      (p * (p + 1) / 2) ^ r * (q * (q + 1) / 2) ^ s := by
  rw [card_crtPairLift, card_pascalResidueFinset, card_pascalResidueFinset]

/-- Convert a pair of residue classes to their canonical finite representatives. -/
def zmodPairFinEquiv (M : ℕ) [NeZero M] :
    (ZMod M × ZMod M) ≃ (Fin M × Fin M) :=
  (ZMod.finEquiv M).symm.prodCongr (ZMod.finEquiv M).symm

/-- The certified two-base CRT Lucas relation, represented by canonical integers. -/
def twoBaseLucasFinset
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Finset (Fin (p ^ r * q ^ s) × Fin (p ^ r * q ^ s)) := by
  letI : NeZero (p ^ r * q ^ s) :=
    ⟨mul_ne_zero (pow_ne_zero_of_prime hp) (pow_ne_zero_of_prime hq)⟩
  exact (crtPairLift (coprime_primePow_primePow hp hq hpq)
    (pascalResidueFinset p r hp) (pascalResidueFinset q s hq)).map
      (zmodPairFinEquiv (p ^ r * q ^ s)).toEmbedding

/-- Formula (240) for the canonical finite representatives used by the semantic bridge. -/
theorem card_twoBaseLucasFinset
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (twoBaseLucasFinset (r := r) (s := s) hp hq hpq).card =
      (p * (p + 1) / 2) ^ r * (q * (q + 1) / 2) ^ s := by
  rw [twoBaseLucasFinset, Finset.card_map]
  exact twoBaseLucasResidue_card hp hq hpq

end

end GoldbachCylinder
