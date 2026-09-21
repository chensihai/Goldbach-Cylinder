import GoldbachCylinder.LucasCRT
import GoldbachCylinder.MacroTriangle

/-!
# Semantic bridge from global truncated pairs to macro blocks

This file identifies an actual ordered pair `(n,k)` below `t*M`, whose local
residue pair belongs to `R`, with the strict-lower/diagonal macro decomposition.
The construction is finite and exact.
-/

namespace GoldbachCylinder

noncomputable section

/-- Reassemble a macro-block index and a local residue. -/
def assembleFin (b : Fin t) (r : Fin M) : Fin (t * M) :=
  finProdFinEquiv (b, r)

@[simp] theorem assembleFin_val (b : Fin t) (r : Fin M) :
    (assembleFin b r : ℕ) = r + M * b := rfl

@[simp] theorem assembleFin_divNat (b : Fin t) (r : Fin M) :
    (assembleFin b r).divNat = b := by
  exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (b, r))

@[simp] theorem assembleFin_modNat (b : Fin t) (r : Fin M) :
    (assembleFin b r).modNat = r := by
  exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (b, r))

@[simp] theorem assembleFin_div_mod (x : Fin (t * M)) :
    assembleFin x.divNat x.modNat = x := by
  exact finProdFinEquiv.apply_symm_apply x

/-- The local admissible pairs that also satisfy ordinary integer order. -/
abbrev DiagonalResidue {M : ℕ} (R : Finset (Fin M × Fin M)) :=
  {x : ↥R // x.1.2 ≤ x.1.1}

/-- Actual truncated ordered pairs with an admissible local residue pair.

The first coordinate is `n`, the second is `k`.  Membership says `k ≤ n`
and that `(n mod M, k mod M)` belongs to the local relation `R`.
-/
abbrev TruncatedResidueTriangle (t M : ℕ) (R : Finset (Fin M × Fin M)) :=
  {x : Fin (t * M) × Fin (t * M) //
    x.2 ≤ x.1 ∧ (x.1.modNat, x.2.modNat) ∈ R}

/-- Assemble the abstract macro decomposition into an actual global pair. -/
def macroToTruncated (t M : ℕ) (R : Finset (Fin M × Fin M)) :
    MacroTriangle t ↥R (DiagonalResidue R) → TruncatedResidueTriangle t M R
  | Sum.inl x =>
      ⟨(assembleFin x.1.1.2 x.2.1.1, assembleFin x.1.1.1 x.2.1.2), by
        constructor
        · change x.2.1.2.1 + M * x.1.1.1.1 ≤ x.2.1.1.1 + M * x.1.1.2.1
          have hblocks : x.1.1.1.1 < x.1.1.2.1 := by
            simpa [strictMacroFinset] using x.1.2
          have hk : x.2.1.2.1 < M := x.2.1.2.2
          exact (calc
            x.2.1.2.1 + M * x.1.1.1.1 < M + M * x.1.1.1.1 :=
              Nat.add_lt_add_right hk _
            _ = M * (x.1.1.1.1 + 1) := by ring
            _ ≤ M * x.1.1.2.1 :=
              Nat.mul_le_mul_left M (Nat.succ_le_of_lt hblocks)
            _ ≤ x.2.1.1.1 + M * x.1.1.2.1 := Nat.le_add_left _ _).le
        · simp [x.2.2]⟩
  | Sum.inr x =>
      ⟨(assembleFin x.1 x.2.1.1.1, assembleFin x.1 x.2.1.1.2), by
        constructor
        · change x.2.1.1.2.1 + M * x.1.1 ≤ x.2.1.1.1.1 + M * x.1.1
          have hlocal : x.2.1.1.2.1 ≤ x.2.1.1.1.1 := x.2.2
          omega
        · simp [x.2.1.2]⟩

/-- Split an actual global pair into its strict-lower or diagonal macro block. -/
def truncatedToMacro (t M : ℕ) (R : Finset (Fin M × Fin M)) :
    TruncatedResidueTriangle t M R → MacroTriangle t ↥R (DiagonalResidue R) := by
  intro z
  let nb := z.1.1.divNat
  let kb := z.1.2.divNat
  let lr : ↥R := ⟨(z.1.1.modNat, z.1.2.modNat), z.2.2⟩
  have hblock : kb ≤ nb := by
    apply Fin.le_iff_val_le_val.mpr
    exact Nat.div_le_div_right z.2.1
  by_cases hstrict : kb < nb
  · exact Sum.inl (⟨(kb, nb), by simpa [strictMacroFinset] using hstrict⟩, lr)
  · have heq : kb = nb := le_antisymm hblock (not_lt.mp hstrict)
    have hlocal : lr.1.2 ≤ lr.1.1 := by
      have hglobal := z.2.1
      change z.1.2.1 ≤ z.1.1.1 at hglobal
      have heqval : z.1.2.divNat.val = z.1.1.divNat.val := by
        exact congrArg Fin.val heq
      have hn := congrArg Fin.val (assembleFin_div_mod z.1.1)
      have hk := congrArg Fin.val (assembleFin_div_mod z.1.2)
      simp only [assembleFin_val] at hn hk
      rw [heqval] at hk
      dsimp [lr] at ⊢
      omega
    exact Sum.inr (nb, ⟨lr, hlocal⟩)

/-- Formula (249): the actual global triangle is exactly the macro decomposition. -/
def truncatedResidueTriangleEquiv (t M : ℕ) (R : Finset (Fin M × Fin M)) :
    TruncatedResidueTriangle t M R ≃
      MacroTriangle t ↥R (DiagonalResidue R) := by
  classical
  exact
    { toFun := truncatedToMacro t M R
      invFun := macroToTruncated t M R
      left_inv := by
        intro z
        unfold truncatedToMacro
        dsimp only
        split
        · apply Subtype.ext
          apply Prod.ext <;> simp [macroToTruncated]
        · apply Subtype.ext
          apply Prod.ext
          · simp [macroToTruncated]
          · dsimp only [macroToTruncated]
            rw [← show z.1.2.divNat = z.1.1.divNat by
              apply le_antisymm
              · apply Fin.le_iff_val_le_val.mpr
                exact Nat.div_le_div_right z.2.1
              · exact not_lt.mp (by assumption : ¬z.1.2.divNat < z.1.1.divNat)]
            simp
      right_inv := by
        intro x
        cases x with
        | inl x =>
            have hstrict : x.1.1.1 < x.1.1.2 := by
              simpa [strictMacroFinset] using x.1.2
            simp [truncatedToMacro, macroToTruncated, hstrict]
        | inr x =>
            simp [truncatedToMacro, macroToTruncated] }

/-- Cardinality corollary of the semantic bridge. -/
theorem card_truncatedResidueTriangle (t M : ℕ) (R : Finset (Fin M × Fin M)) :
    Fintype.card (TruncatedResidueTriangle t M R) =
      Nat.choose t 2 * R.card + t * Fintype.card (DiagonalResidue R) := by
  rw [Fintype.card_congr (truncatedResidueTriangleEquiv t M R)]
  simpa using card_macroTriangle t ↥R (DiagonalResidue R)

/-- The actual truncated triangle for the certified two-base Lucas CRT relation. -/
abbrev TwoBaseTruncatedTriangle
    {p q r s : ℕ} (t : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :=
  TruncatedResidueTriangle t (p ^ r * q ^ s)
    (twoBaseLucasFinset (r := r) (s := s) hp hq hpq)

/-- Its genuinely ordered diagonal local block. -/
abbrev TwoBaseDiagonalResidue
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :=
  DiagonalResidue (twoBaseLucasFinset (r := r) (s := s) hp hq hpq)

/-- Formula (249), specialized to the actual certified two-base Lucas relation. -/
def twoBaseTruncatedTriangleEquiv
    {p q r s : ℕ} (t : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    TwoBaseTruncatedTriangle (r := r) (s := s) t hp hq hpq ≃
      MacroTriangle t ↥(twoBaseLucasFinset (r := r) (s := s) hp hq hpq)
        (TwoBaseDiagonalResidue (r := r) (s := s) hp hq hpq) :=
  truncatedResidueTriangleEquiv t (p ^ r * q ^ s)
    (twoBaseLucasFinset (r := r) (s := s) hp hq hpq)

/-- Exact card formula for the genuine truncated two-base triangle.

The complete local mass is closed-form; the only remaining finite unknown is
the ordinary-order diagonal block.
-/
theorem card_twoBaseTruncatedTriangle
    {p q r s : ℕ} (t : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Fintype.card (TwoBaseTruncatedTriangle (r := r) (s := s) t hp hq hpq) =
      Nat.choose t 2 *
          ((p * (p + 1) / 2) ^ r * (q * (q + 1) / 2) ^ s) +
        t * Fintype.card (TwoBaseDiagonalResidue (r := r) (s := s) hp hq hpq) := by
  rw [card_truncatedResidueTriangle, card_twoBaseLucasFinset]

end

end GoldbachCylinder
