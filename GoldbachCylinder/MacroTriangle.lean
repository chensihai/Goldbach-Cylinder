import Mathlib

/-!
# Exact macro-triangle decomposition

`R` is the type of admissible residue pairs in a full off-diagonal macro block.
`H` is the subtype that also satisfies the local diagonal order condition.
The decomposition has one copy of `R` for each strict lower macro block and
one copy of `H` for each diagonal macro block.
-/

namespace GoldbachCylinder

noncomputable section

/-- Strictly lower macro-block indices as a finite set. -/
def strictMacroFinset (t : ℕ) : Finset (Fin t × Fin t) :=
  (Finset.univ.product Finset.univ).filter fun x => x.1 < x.2

abbrev StrictMacroIndex (t : ℕ) := ↥(strictMacroFinset t)

/-- Exact combinatorial decomposition of a periodic triangular region. -/
abbrev MacroTriangle (t : ℕ) (R H : Type*) :=
  (StrictMacroIndex t × R) ⊕ (Fin t × H)

theorem card_strictMacroIndex (t : ℕ) :
    Fintype.card (StrictMacroIndex t) = Nat.choose t 2 := by
  rw [Fintype.card_coe]
  simpa [strictMacroFinset] using (Fintype.card_product_filter_lt (α := Fin t))

/-- Formula (245): strict macro blocks plus diagonal residue triangles. -/
theorem card_macroTriangle (t : ℕ) (R H : Type*)
    [Fintype R] [Fintype H] :
    Fintype.card (MacroTriangle t R H) =
      Nat.choose t 2 * Fintype.card R + t * Fintype.card H := by
  simp only [MacroTriangle, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, card_strictMacroIndex]

/-- Formula (246), lower bound. -/
theorem card_macroTriangle_lower (t : ℕ) (R H : Type*)
    [Fintype R] [Fintype H] :
    Nat.choose t 2 * Fintype.card R ≤ Fintype.card (MacroTriangle t R H) := by
  rw [card_macroTriangle]
  omega

/-- Formula (246), upper bound under the natural diagonal inclusion bound. -/
theorem card_macroTriangle_upper (t : ℕ) (R H : Type*)
    [Fintype R] [Fintype H] (hHR : Fintype.card H ≤ Fintype.card R) :
    Fintype.card (MacroTriangle t R H) ≤
      (Nat.choose t 2 + t) * Fintype.card R := by
  rw [card_macroTriangle]
  nlinarith

/-- Centered integer error corresponding to formulas (247)--(248). -/
def macroTriangleError (t J H : ℕ) : ℤ :=
  2 * (Nat.choose t 2 * J + t * H : ℕ) - (t * t * J : ℕ)

/-- Twice the centered error is bounded by `tJ`; this avoids division in `ℕ`. -/
theorem abs_macroTriangleError_le (t J H : ℕ) (hH : H ≤ J) :
    |macroTriangleError t J H| ≤ (t * J : ℕ) := by
  have herr : macroTriangleError t J H =
      (t : ℤ) * (2 * (H : ℤ) - (J : ℤ)) := by
    have hchooseNat : 2 * Nat.choose t 2 = t * (t - 1) := by
      rw [Nat.choose_two_right, Nat.mul_comm 2]
      exact Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self t)
    have hchooseInt : 2 * (Nat.choose t 2 : ℤ) =
        (t : ℤ) * ((t - 1 : ℕ) : ℤ) := by
      exact_mod_cast hchooseNat
    have hpred : (t : ℤ) * ((t - 1 : ℕ) : ℤ) =
        (t : ℤ) * (t : ℤ) - (t : ℤ) := by
      cases t with
      | zero => simp
      | succ n =>
          simp
          ring
    simp only [macroTriangleError]
    push_cast
    calc
      2 * (↑(t.choose 2) * ↑J + ↑t * ↑H) - ↑t * ↑t * ↑J =
          (2 * (t.choose 2 : ℤ)) * (J : ℤ) +
            2 * (t : ℤ) * (H : ℤ) - (t : ℤ) * (t : ℤ) * (J : ℤ) := by ring
      _ = (t : ℤ) * (2 * (H : ℤ) - (J : ℤ)) := by
        rw [hchooseInt, hpred]
        ring
  rw [herr, abs_mul]
  have hinner : |2 * (H : ℤ) - (J : ℤ)| ≤ (J : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  rw [abs_of_nonneg (Int.natCast_nonneg t)]
  simpa using (mul_le_mul_of_nonneg_left hinner (Int.natCast_nonneg t))

end

end GoldbachCylinder
