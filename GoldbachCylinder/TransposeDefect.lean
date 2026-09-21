import GoldbachCylinder.SemanticBridge

/-!
# Transpose defect of a finite ordered relation

The unknown diagonal macro-block is recentered as a signed lower/upper order
defect.  Everything in this file is a finite exact identity.
-/

namespace GoldbachCylinder

noncomputable section

def lowerCount {M : ℕ} (R : Finset (Fin M × Fin M)) : ℕ :=
  (R.filter fun x => x.2 < x.1).card

def upperCount {M : ℕ} (R : Finset (Fin M × Fin M)) : ℕ :=
  (R.filter fun x => x.1 < x.2).card

def diagonalCount {M : ℕ} (R : Finset (Fin M × Fin M)) : ℕ :=
  (R.filter fun x => x.1 = x.2).card

def lowerDiagonalCount {M : ℕ} (R : Finset (Fin M × Fin M)) : ℕ :=
  (R.filter fun x => x.2 ≤ x.1).card

def upperDiagonalCount {M : ℕ} (R : Finset (Fin M × Fin M)) : ℕ :=
  (R.filter fun x => x.1 ≤ x.2).card

/-- Transpose a finite relation by swapping its two coordinates. -/
def transposeRelation {M : ℕ} (R : Finset (Fin M × Fin M)) :
    Finset (Fin M × Fin M) :=
  R.map (Equiv.prodComm (Fin M) (Fin M)).toEmbedding

@[simp] theorem card_transposeRelation {M : ℕ} (R : Finset (Fin M × Fin M)) :
    (transposeRelation R).card = R.card := by
  simp [transposeRelation]

theorem lowerDiagonalCount_transpose {M : ℕ} (R : Finset (Fin M × Fin M)) :
    lowerDiagonalCount (transposeRelation R) = upperDiagonalCount R := by
  classical
  have heq : (transposeRelation R).filter (fun x => x.2 ≤ x.1) =
      (R.filter fun x => x.1 ≤ x.2).map
        (Equiv.prodComm (Fin M) (Fin M)).toEmbedding := by
    ext x
    simp [transposeRelation]
  rw [lowerDiagonalCount, upperDiagonalCount, heq, Finset.card_map]

private def diagonalEmbedding (M : ℕ) : Fin M ↪ (Fin M × Fin M) where
  toFun a := (a, a)
  inj' := fun _ _ h => congrArg Prod.fst h

theorem diagonalCount_eq_card_of_all {M : ℕ} (R : Finset (Fin M × Fin M))
    (hdiag : ∀ a : Fin M, (a, a) ∈ R) : diagonalCount R = M := by
  classical
  have heq : R.filter (fun x => x.1 = x.2) =
      Finset.univ.map (diagonalEmbedding M) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, heq⟩
      exact ⟨x.1, Prod.ext rfl heq⟩
    · rintro ⟨a, rfl⟩
      exact ⟨hdiag a, rfl⟩
  rw [diagonalCount, heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem card_lower_add_diagonal_add_upper {M : ℕ}
    (R : Finset (Fin M × Fin M)) :
    lowerCount R + diagonalCount R + upperCount R = R.card := by
  classical
  have hpartition :
      (R.filter fun x => ¬ x.2 < x.1).filter (fun x => ¬ x.1 = x.2) =
        R.filter (fun x => x.1 < x.2) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, hnot⟩, hne⟩
      exact ⟨hx, lt_of_le_of_ne (not_lt.mp hnot) hne⟩
    · rintro ⟨hx, hlt⟩
      exact ⟨⟨hx, not_lt_of_ge hlt.le⟩, ne_of_lt hlt⟩
  have h1 := Finset.card_filter_add_card_filter_not (s := R) (fun x => x.2 < x.1)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := R.filter fun x => ¬ x.2 < x.1) (fun x => x.1 = x.2)
  rw [hpartition] at h2
  have hdiag :
      ((R.filter fun x => ¬ x.2 < x.1).filter fun x => x.1 = x.2) =
        R.filter (fun x => x.1 = x.2) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, hnot⟩, heq⟩
      exact ⟨hx, heq⟩
    · rintro ⟨hx, heq⟩
      exact ⟨⟨hx, by simp [heq]⟩, heq⟩
  dsimp [lowerCount, diagonalCount, upperCount] at h1 h2 ⊢
  rw [hdiag] at h2
  omega

theorem lowerDiagonalCount_eq {M : ℕ} (R : Finset (Fin M × Fin M)) :
    lowerDiagonalCount R = diagonalCount R + lowerCount R := by
  classical
  rw [lowerDiagonalCount, diagonalCount, lowerCount]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := R.filter fun x => x.2 ≤ x.1) (fun x => x.1 = x.2)
  have hstrict :
      ((R.filter fun x => x.2 ≤ x.1).filter fun x => ¬ x.1 = x.2) =
        R.filter (fun x => x.2 < x.1) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, hle⟩, hne⟩
      exact ⟨hx, lt_of_le_of_ne hle (Ne.symm hne)⟩
    · rintro ⟨hx, hlt⟩
      exact ⟨⟨hx, hlt.le⟩, ne_of_gt hlt⟩
  have hdiag :
      ((R.filter fun x => x.2 ≤ x.1).filter fun x => x.1 = x.2) =
        R.filter (fun x => x.1 = x.2) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, hle⟩, heq⟩
      exact ⟨hx, heq⟩
    · rintro ⟨hx, heq⟩
      exact ⟨⟨hx, by simp [heq]⟩, heq⟩
  rw [hdiag, hstrict] at hsplit
  omega

theorem upperDiagonalCount_eq {M : ℕ} (R : Finset (Fin M × Fin M)) :
    upperDiagonalCount R = diagonalCount R + upperCount R := by
  classical
  rw [upperDiagonalCount, diagonalCount, upperCount]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := R.filter fun x => x.1 ≤ x.2) (fun x => x.1 = x.2)
  have hstrict :
      ((R.filter fun x => x.1 ≤ x.2).filter fun x => ¬ x.1 = x.2) =
        R.filter (fun x => x.1 < x.2) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, hle⟩, hne⟩
      exact ⟨hx, lt_of_le_of_ne hle hne⟩
    · rintro ⟨hx, hlt⟩
      exact ⟨⟨hx, hlt.le⟩, ne_of_lt hlt⟩
  have hdiag :
      ((R.filter fun x => x.1 ≤ x.2).filter fun x => x.1 = x.2) =
        R.filter (fun x => x.1 = x.2) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, hle⟩, heq⟩
      exact ⟨hx, heq⟩
    · rintro ⟨hx, heq⟩
      exact ⟨⟨hx, by simp [heq]⟩, heq⟩
  rw [hdiag, hstrict] at hsplit
  omega

/-- Signed ordinary-order asymmetry.  `upperDiagonalCount` is exactly the
lower-triangle count of the transposed relation. -/
def orderDefect {M : ℕ} (R : Finset (Fin M × Fin M)) : ℤ :=
  (lowerDiagonalCount R : ℤ) - (upperDiagonalCount R : ℤ)

theorem transpose_card_identity {M : ℕ} (R : Finset (Fin M × Fin M)) :
    lowerDiagonalCount R + upperDiagonalCount R = R.card + diagonalCount R := by
  rw [lowerDiagonalCount_eq, upperDiagonalCount_eq,
    ← card_lower_add_diagonal_add_upper R]
  omega

theorem two_mul_lowerDiagonalCount_eq {M : ℕ} (R : Finset (Fin M × Fin M)) :
    2 * (lowerDiagonalCount R : ℤ) =
      (R.card : ℤ) + diagonalCount R + orderDefect R := by
  have h := transpose_card_identity R
  dsimp [orderDefect]
  omega

theorem abs_orderDefect_le {M : ℕ} (R : Finset (Fin M × Fin M)) :
    |orderDefect R| ≤ (R.card - diagonalCount R : ℕ) := by
  rw [orderDefect, lowerDiagonalCount_eq, upperDiagonalCount_eq]
  have hpart := card_lower_add_diagonal_add_upper R
  rw [abs_le]
  constructor <;> omega

theorem orderDefect_emod_two {M : ℕ} (R : Finset (Fin M × Fin M)) :
    orderDefect R % 2 = ((R.card - diagonalCount R : ℕ) : ℤ) % 2 := by
  rw [orderDefect, lowerDiagonalCount_eq, upperDiagonalCount_eq]
  have hpart := card_lower_add_diagonal_add_upper R
  have hsub : R.card - diagonalCount R = lowerCount R + upperCount R := by omega
  rw [hsub]
  push_cast
  omega

private def diagonalResidueEquiv {M : ℕ} (R : Finset (Fin M × Fin M)) :
    DiagonalResidue R ≃ ↥(R.filter fun x => x.2 ≤ x.1) where
  toFun x := ⟨x.1.1, Finset.mem_filter.mpr ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, (Finset.mem_filter.mp x.2).1⟩, (Finset.mem_filter.mp x.2).2⟩
  left_inv x := by rfl
  right_inv x := by rfl

theorem card_diagonalResidue_eq {M : ℕ} (R : Finset (Fin M × Fin M)) :
    Fintype.card (DiagonalResidue R) = lowerDiagonalCount R := by
  rw [Fintype.card_congr (diagonalResidueEquiv R), Fintype.card_coe]
  rfl

/-- Formula (271), for any finite relation: subtracting the full diagonal
contribution leaves exactly the signed order defect. -/
theorem truncatedTriangle_centered_eq {M t : ℕ} (R : Finset (Fin M × Fin M)) :
    (2 * Fintype.card (TruncatedResidueTriangle t M R) : ℤ) -
        (t * t * R.card : ℕ) - (t * diagonalCount R : ℕ) =
      (t : ℤ) * orderDefect R := by
  rw [card_truncatedResidueTriangle]
  rw [card_diagonalResidue_eq]
  have hdef := two_mul_lowerDiagonalCount_eq R
  have hchooseNat : 2 * Nat.choose t 2 = t * (t - 1) := by
    rw [Nat.choose_two_right, Nat.mul_comm 2]
    exact Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self t)
  push_cast
  have hchooseInt : 2 * (Nat.choose t 2 : ℤ) =
      (t : ℤ) * ((t - 1 : ℕ) : ℤ) := by exact_mod_cast hchooseNat
  have hpred : (t : ℤ) * ((t - 1 : ℕ) : ℤ) =
      (t : ℤ) * (t : ℤ) - (t : ℤ) := by
    cases t with
    | zero => simp
    | succ n => simp; ring
  calc
    2 * ((t.choose 2 : ℤ) * R.card + (t : ℤ) * lowerDiagonalCount R) -
          (t : ℤ) * t * R.card - (t : ℤ) * diagonalCount R =
        (2 * (t.choose 2 : ℤ)) * R.card +
          2 * (t : ℤ) * lowerDiagonalCount R -
          (t : ℤ) * t * R.card - (t : ℤ) * diagonalCount R := by ring
    _ = (t : ℤ) * orderDefect R := by
      rw [hchooseInt, hpred]
      linear_combination (t : ℤ) * hdef

theorem abs_truncatedTriangle_centered_le {M t : ℕ}
    (R : Finset (Fin M × Fin M)) :
    |(2 * Fintype.card (TruncatedResidueTriangle t M R) : ℤ) -
        (t * t * R.card : ℕ) - (t * diagonalCount R : ℕ)| ≤
      (t * (R.card - diagonalCount R) : ℕ) := by
  rw [truncatedTriangle_centered_eq, abs_mul]
  have h := abs_orderDefect_le R
  rw [abs_of_nonneg (Int.natCast_nonneg t)]
  simpa using mul_le_mul_of_nonneg_left h (Int.natCast_nonneg t)

theorem twoBaseLucasDiagonal_card
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    diagonalCount (twoBaseLucasFinset (r := r) (s := s) hp hq hpq) =
      p ^ r * q ^ s := by
  apply diagonalCount_eq_card_of_all
  exact diagonal_mem_twoBaseLucasFinset (r := r) (s := s) hp hq hpq

theorem twoBaseLucasDefect_identity
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    2 * (lowerDiagonalCount
      (twoBaseLucasFinset (r := r) (s := s) hp hq hpq) : ℤ) =
      ((p * (p + 1) / 2) ^ r * (q * (q + 1) / 2) ^ s : ℕ) +
        (p ^ r * q ^ s : ℕ) +
        orderDefect (twoBaseLucasFinset (r := r) (s := s) hp hq hpq) := by
  rw [two_mul_lowerDiagonalCount_eq, card_twoBaseLucasFinset,
    twoBaseLucasDiagonal_card]

theorem twoBaseLucasDefect_abs_le
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    |orderDefect (twoBaseLucasFinset (r := r) (s := s) hp hq hpq)| ≤
      (((p * (p + 1) / 2) ^ r * (q * (q + 1) / 2) ^ s) -
        p ^ r * q ^ s : ℕ) := by
  simpa only [card_twoBaseLucasFinset, twoBaseLucasDiagonal_card] using
    abs_orderDefect_le (twoBaseLucasFinset (r := r) (s := s) hp hq hpq)

theorem twoBaseLucasDefect_emod_two
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    orderDefect (twoBaseLucasFinset (r := r) (s := s) hp hq hpq) % 2 =
      ((((p * (p + 1) / 2) ^ r * (q * (q + 1) / 2) ^ s) -
        p ^ r * q ^ s : ℕ) : ℤ) % 2 := by
  simpa only [card_twoBaseLucasFinset, twoBaseLucasDiagonal_card] using
    orderDefect_emod_two (twoBaseLucasFinset (r := r) (s := s) hp hq hpq)

theorem twoBaseTruncatedTriangle_centered_eq
    {p q r s : ℕ} (t : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (2 * Fintype.card
      (TwoBaseTruncatedTriangle (r := r) (s := s) t hp hq hpq) : ℤ) -
        (t * t * ((p * (p + 1) / 2) ^ r * (q * (q + 1) / 2) ^ s) : ℕ) -
        (t * (p ^ r * q ^ s) : ℕ) =
      (t : ℤ) * orderDefect
        (twoBaseLucasFinset (r := r) (s := s) hp hq hpq) := by
  simpa only [card_twoBaseLucasFinset, twoBaseLucasDiagonal_card] using
    truncatedTriangle_centered_eq
      (R := twoBaseLucasFinset (r := r) (s := s) hp hq hpq) (t := t)

theorem twoBaseTruncatedTriangle_centered_abs_le
    {p q r s : ℕ} (t : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    |(2 * Fintype.card
      (TwoBaseTruncatedTriangle (r := r) (s := s) t hp hq hpq) : ℤ) -
        (t * t * ((p * (p + 1) / 2) ^ r * (q * (q + 1) / 2) ^ s) : ℕ) -
        (t * (p ^ r * q ^ s) : ℕ)| ≤
      (t * (((p * (p + 1) / 2) ^ r * (q * (q + 1) / 2) ^ s) -
        p ^ r * q ^ s) : ℕ) := by
  simpa only [card_twoBaseLucasFinset, twoBaseLucasDiagonal_card] using
    abs_truncatedTriangle_centered_le
      (R := twoBaseLucasFinset (r := r) (s := s) hp hq hpq) (t := t)

end

end GoldbachCylinder
