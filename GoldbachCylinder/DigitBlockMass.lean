import Mathlib

/-!
# Exact mass of a complete digit block

This file proves the finite identity underlying the single-base Lucas mass.
It uses only quotient/remainder arithmetic.  No asymptotic statement is made.
-/

open scoped BigOperators

namespace GoldbachCylinder

/-- Product of `(digit + 1)` over the lowest `d` base-`b` digits. -/
def digitWeight (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | d + 1, n => (n % b + 1) * digitWeight b d (n / b)

theorem digitWeight_mul_add {b d m a : ℕ} (hb : 0 < b) (ha : a < b) :
    digitWeight b (d + 1) (b * m + a) = (a + 1) * digitWeight b d m := by
  rw [digitWeight, show b * m + a = a + b * m by omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
    Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt ha, Nat.zero_add]

theorem sum_range_pow_succ_eq_sum_product
    {R : Type*} [AddCommMonoid R] (b d : ℕ) (f : ℕ → R) :
    (∑ n ∈ Finset.range (b ^ (d + 1)), f n) =
      ∑ m ∈ Finset.range (b ^ d), ∑ a ∈ Finset.range b, f (b * m + a) := by
  rw [pow_succ]
  calc
    (∑ n ∈ Finset.range (b ^ d * b), f n) =
        ∑ n : Fin (b ^ d * b), f n := by rw [Fin.sum_univ_eq_sum_range]
    _ = ∑ x : Fin (b ^ d) × Fin b, f (finProdFinEquiv x) := by
      exact Fintype.sum_equiv finProdFinEquiv.symm
        (fun n => f n) (fun x => f (finProdFinEquiv x)) (by
          intro x
          exact congrArg f (Nat.mod_add_div x b).symm)
    _ = ∑ m ∈ Finset.range (b ^ d), ∑ a ∈ Finset.range b, f (b * m + a) := by
      rw [Fintype.sum_prod_type]
      change (∑ m : Fin (b ^ d), ∑ a : Fin b, f (↑a + b * ↑m)) = _
      rw [Fin.sum_univ_eq_sum_range
        (fun m => ∑ a : Fin b, f (↑a + b * m)) (b ^ d)]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Fin.sum_univ_eq_sum_range (fun a => f (a + b * m)) b]
      simp [Nat.add_comm]

theorem sum_range_add_one (b : ℕ) :
    (∑ a ∈ Finset.range b, (a + 1)) = b * (b + 1) / 2 := by
  calc
    (∑ a ∈ Finset.range b, (a + 1)) = ∑ a ∈ Finset.range (b + 1), a := by
      rw [Finset.sum_range_succ']
      simp
    _ = (b + 1) * ((b + 1) - 1) / 2 := Finset.sum_range_id _
    _ = b * (b + 1) / 2 := by simp [Nat.mul_comm]

/-- Exact single-base mass over a complete base-`b` block. -/
theorem sum_digitWeight_range_pow (b d : ℕ) (hb : 0 < b) :
    (∑ n ∈ Finset.range (b ^ d), digitWeight b d n) =
      (b * (b + 1) / 2) ^ d := by
  induction d with
  | zero => simp [digitWeight]
  | succ d ih =>
      rw [sum_range_pow_succ_eq_sum_product]
      calc
        (∑ m ∈ Finset.range (b ^ d), ∑ a ∈ Finset.range b,
          digitWeight b (d + 1) (b * m + a)) =
            ∑ m ∈ Finset.range (b ^ d), ∑ a ∈ Finset.range b,
              (a + 1) * digitWeight b d m := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro a ha
          exact digitWeight_mul_add hb (Finset.mem_range.mp ha)
        _ = (b * (b + 1) / 2) ^ d * (b * (b + 1) / 2) := by
          simp_rw [← Finset.sum_mul]
          rw [← Finset.mul_sum, sum_range_add_one, ih]
          exact Nat.mul_comm _ _
        _ = (b * (b + 1) / 2) ^ (d + 1) := by
          simpa [Nat.mul_comm] using (pow_succ (b * (b + 1) / 2) d).symm

/-- The complete digit-box pair count, stated as the sum of row masses. -/
def digitBoxPairCount (b d : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (b ^ d), digitWeight b d n

theorem digitBoxPairCount_eq (b d : ℕ) (hb : 0 < b) :
    digitBoxPairCount b d = (b * (b + 1) / 2) ^ d := by
  exact sum_digitWeight_range_pow b d hb

end GoldbachCylinder
