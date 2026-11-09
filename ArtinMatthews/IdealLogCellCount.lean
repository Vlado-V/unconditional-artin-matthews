module

public import ArtinMatthews.IdealLogCellPartition


set_option backward.privateInPublic true
@[expose] public section

/-! The number of occupied log cells is derived from the actual selected
prime products; no cell-count bound is assumed. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem idealSelectedProduct_log_le (P : I → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) {Y : ℝ}
    (hupper : ∀ i p, p ∈ P i → (p : ℝ) ≤ Real.exp Y) (a : IdealSelectedLabels P) :
    Real.log (idealSelectedProduct a) ≤ (Fintype.card I : ℝ)*Y := by
  have hp (i : I) : 0 < ((a i).val : ℝ) := by exact_mod_cast (hP i _ (a i).property).pos
  simp only [idealSelectedProduct, Nat.cast_prod]
  rw [Real.log_prod (fun i _ => (hp i).ne')]
  calc
    _ ≤ ∑ _i : I, Y := by
      apply sum_le_sum
      intro i _
      exact (Real.log_le_iff_le_exp (hp i)).mpr (hupper i _ (a i).property)
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

theorem idealLogCells_card_le (P : I → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) {Y h : ℝ} (hY : 0 ≤ Y) (hh : 0 < h)
    (hupper : ∀ i p, p ∈ P i → (p : ℝ) ≤ Real.exp Y) :
    ((idealLogCells P h).card : ℝ) ≤ 1 + (Fintype.card I : ℝ)*Y/h := by
  let R := (Fintype.card I : ℝ)*Y/h
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsub : idealLogCells P h ⊆ Icc 0 ⌊R⌋ := by
    intro j hj
    obtain ⟨a, _, rfl⟩ := mem_image.mp hj
    have hp : 1 ≤ (idealSelectedProduct a : ℝ) := by
      exact_mod_cast idealSelectedProduct_pos hP a
    have hlo : 0 ≤ Real.log (idealSelectedProduct a)/h :=
      div_nonneg (Real.log_nonneg hp) hh.le
    have hhi : Real.log (idealSelectedProduct a)/h ≤ R :=
      div_le_div_of_nonneg_right (idealSelectedProduct_log_le P hP hupper a) hh.le
    exact mem_Icc.mpr ⟨Int.floor_nonneg.mpr hlo, Int.floor_mono hhi⟩
  have hn : 0 ≤ ⌊R⌋ + 1 := by have := Int.floor_nonneg.mpr hR; omega
  have ht : (((⌊R⌋+1).toNat : ℕ) : ℝ) = ((⌊R⌋+1 : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  calc
    _ ≤ ((Icc 0 ⌊R⌋).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ = (⌊R⌋ : ℝ)+1 := by rw [Int.card_Icc, sub_zero, ht, Int.cast_add, Int.cast_one]
    _ ≤ 1+R := by have := Int.floor_le R; linarith

theorem idealDiscardedCellMass_source_le (P : I → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) {Y h ξ : ℝ} (hY : 0 ≤ Y) (hh : 0 < h)
    (hξ : 0 ≤ ξ) (hupper : ∀ i p, p ∈ P i → (p : ℝ) ≤ Real.exp Y) :
    idealDiscardedCellMass P h ξ ≤ (1+(Fintype.card I : ℝ)*Y/h)*ξ :=
  (idealDiscardedCellMass_le P h hξ).trans
    (mul_le_mul_of_nonneg_right (idealLogCells_card_le P hP hY hh hupper) hξ)

end
end ArtinMatthews
