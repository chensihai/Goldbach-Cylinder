import GoldbachCylinder.TransposeDefect

/-!
# Exchange invariance of the two-base Lucas relation

Swapping the two coprime prime-power factors preserves the canonical integer
representatives.  The transport below is `Fin.cast` along multiplication
commutativity, so it preserves ordinary order as well as relation membership.
-/

namespace GoldbachCylinder

noncomputable section

def mulCommFinEquiv (P Q : ℕ) : Fin (P * Q) ≃ Fin (Q * P) :=
  { toFun := Fin.cast (Nat.mul_comm P Q)
    invFun := Fin.cast (Nat.mul_comm Q P)
    left_inv := fun _ => Fin.ext rfl
    right_inv := fun _ => Fin.ext rfl }

@[simp] theorem mulCommFinEquiv_val (P Q : ℕ) (a : Fin (P * Q)) :
    (mulCommFinEquiv P Q a : ℕ) = a := by
  exact Fin.val_cast (Nat.mul_comm P Q) a

def mulCommPairEquiv (P Q : ℕ) :
    (Fin (P * Q) × Fin (P * Q)) ≃ (Fin (Q * P) × Fin (Q * P)) :=
  (mulCommFinEquiv P Q).prodCongr (mulCommFinEquiv P Q)

private theorem finEquiv_eq_natCast (M : ℕ) [NeZero M] (a : Fin M) :
    ZMod.finEquiv M a = (a.1 : ZMod M) := by
  cases M with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ M =>
      apply ZMod.val_injective (M + 1)
      change (a : ℕ) = ((a.1 : ZMod (M + 1))).val
      simp [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]

theorem mem_twoBaseLucasFinset_iff
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (x : Fin (p ^ r * q ^ s) × Fin (p ^ r * q ^ s)) :
    x ∈ twoBaseLucasFinset (r := r) (s := s) hp hq hpq ↔
      (((x.1 : ℕ) : ZMod (p ^ r)), ((x.2 : ℕ) : ZMod (p ^ r))) ∈
          pascalResidueFinset p r hp ∧
        (((x.1 : ℕ) : ZMod (q ^ s)), ((x.2 : ℕ) : ZMod (q ^ s))) ∈
          pascalResidueFinset q s hq := by
  classical
  let _ : NeZero (p ^ r * q ^ s) :=
    ⟨mul_ne_zero (pow_ne_zero r hp.ne_zero) (pow_ne_zero s hq.ne_zero)⟩
  rw [twoBaseLucasFinset, Finset.mem_map_equiv, crtPairLift,
    Finset.mem_map_equiv]
  simp [zmodPairFinEquiv, crtPairEquiv, finEquiv_eq_natCast]

theorem mem_twoBaseLucasFinset_exchange
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (x : Fin (p ^ r * q ^ s) × Fin (p ^ r * q ^ s)) :
    x ∈ twoBaseLucasFinset (r := r) (s := s) hp hq hpq ↔
      mulCommPairEquiv (p ^ r) (q ^ s) x ∈
        twoBaseLucasFinset (r := s) (s := r) hq hp hpq.symm := by
  rw [mem_twoBaseLucasFinset_iff, mem_twoBaseLucasFinset_iff]
  simp [mulCommPairEquiv, and_comm]

/-- Formula (278): exchange of the two prime-power factors gives an equivalence
of the actual canonical integer relations. -/
def twoBaseLucasRelationExchangeEquiv
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ↥(twoBaseLucasFinset (r := r) (s := s) hp hq hpq) ≃
      ↥(twoBaseLucasFinset (r := s) (s := r) hq hp hpq.symm) where
  toFun x := ⟨mulCommPairEquiv (p ^ r) (q ^ s) x.1,
    (mem_twoBaseLucasFinset_exchange hp hq hpq x.1).mp x.2⟩
  invFun x := ⟨mulCommPairEquiv (q ^ s) (p ^ r) x.1,
    (mem_twoBaseLucasFinset_exchange hq hp hpq.symm x.1).mp x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> rfl

/-- Exchange preserves the ordinary lower-triangle condition. -/
def twoBaseLucasDiagonalExchangeEquiv
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    TwoBaseDiagonalResidue (r := r) (s := s) hp hq hpq ≃
      TwoBaseDiagonalResidue (r := s) (s := r) hq hp hpq.symm where
  toFun x := ⟨twoBaseLucasRelationExchangeEquiv hp hq hpq x.1, by
    exact x.2⟩
  invFun x := ⟨(twoBaseLucasRelationExchangeEquiv hp hq hpq).symm x.1, by
    exact x.2⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem twoBaseLucas_card_exchange
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (twoBaseLucasFinset (r := r) (s := s) hp hq hpq).card =
      (twoBaseLucasFinset (r := s) (s := r) hq hp hpq.symm).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (twoBaseLucasRelationExchangeEquiv hp hq hpq)

theorem twoBaseLucas_lowerDiagonalCount_exchange
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    lowerDiagonalCount (twoBaseLucasFinset (r := r) (s := s) hp hq hpq) =
      lowerDiagonalCount
        (twoBaseLucasFinset (r := s) (s := r) hq hp hpq.symm) := by
  rw [← card_diagonalResidue_eq, ← card_diagonalResidue_eq]
  exact Fintype.card_congr (twoBaseLucasDiagonalExchangeEquiv hp hq hpq)

theorem twoBaseLucas_upperDiagonalCount_exchange
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    upperDiagonalCount (twoBaseLucasFinset (r := r) (s := s) hp hq hpq) =
      upperDiagonalCount
        (twoBaseLucasFinset (r := s) (s := r) hq hp hpq.symm) := by
  have hleft := transpose_card_identity
    (twoBaseLucasFinset (r := r) (s := s) hp hq hpq)
  have hright := transpose_card_identity
    (twoBaseLucasFinset (r := s) (s := r) hq hp hpq.symm)
  have hJ := twoBaseLucas_card_exchange (r := r) (s := s) hp hq hpq
  have hH := twoBaseLucas_lowerDiagonalCount_exchange (r := r) (s := s) hp hq hpq
  have hDleft := twoBaseLucasDiagonal_card (r := r) (s := s) hp hq hpq
  have hDright := twoBaseLucasDiagonal_card (r := s) (s := r) hq hp hpq.symm
  have hM : p ^ r * q ^ s = q ^ s * p ^ r := Nat.mul_comm _ _
  omega

/-- Formula (279): the signed defect is invariant under base/depth exchange. -/
theorem twoBaseLucas_orderDefect_exchange
    {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    orderDefect (twoBaseLucasFinset (r := r) (s := s) hp hq hpq) =
      orderDefect
        (twoBaseLucasFinset (r := s) (s := r) hq hp hpq.symm) := by
  rw [orderDefect, orderDefect, twoBaseLucas_lowerDiagonalCount_exchange hp hq hpq,
    twoBaseLucas_upperDiagonalCount_exchange hp hq hpq]

theorem twoBaseTruncatedTriangle_card_exchange
    {p q r s : ℕ} (t : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Fintype.card (TwoBaseTruncatedTriangle (r := r) (s := s) t hp hq hpq) =
      Fintype.card
        (TwoBaseTruncatedTriangle (r := s) (s := r) t hq hp hpq.symm) := by
  rw [card_twoBaseTruncatedTriangle, card_twoBaseTruncatedTriangle]
  have hH := Fintype.card_congr
    (twoBaseLucasDiagonalExchangeEquiv (r := r) (s := s) hp hq hpq)
  rw [hH]
  ring

end

end GoldbachCylinder
