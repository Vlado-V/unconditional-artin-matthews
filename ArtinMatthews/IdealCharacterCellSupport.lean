module

public import ArtinMatthews.IdealCharacterCellApply


set_option backward.privateInPublic true
@[expose] public section

/-! Kernel localization propagates the support of arbitrary ordered-tuple
functions before the minor-arc coefficient collapse. -/
namespace ArtinMatthews
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem idealCharacterCellApply_log_support (P : I → Finset ℕ) (Q : ℕ)
    {h ξ a b : ℝ} (hh : 0 < h) (f : IdealSelectedLabels P → ℂ)
    (hf : ∀ z, f z ≠ 0 → a ≤ Real.log (idealSelectedProduct z) ∧
      Real.log (idealSelectedProduct z) ≤ b) (x : IdealSelectedLabels P)
    (hx : idealCharacterCellApply P Q h ξ f x ≠ 0) :
    a-h < Real.log (idealSelectedProduct x) ∧ Real.log (idealSelectedProduct x) < b+h := by
  obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  have hfz : f z ≠ 0 := by
    intro he
    apply hz
    rw [he, mul_zero]
  have hkernel : idealCharacterCellKernel P Q h ξ z x ≠ 0 := by
    intro he
    apply hz
    rw [he, mul_zero, zero_mul]
  have hs := idealCharacterCellKernel_support P Q hh z x hkernel
  have hsupport := hf z hfz
  rw [abs_lt] at hs
  constructor <;> linarith

theorem idealCharacterCellApply_product_support (P : I → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (Q : ℕ) {h ξ U V : ℝ}
    (hh : 0 < h) (hU : 0 < U) (hV : 0 < V) (f : IdealSelectedLabels P → ℂ)
    (hf : ∀ z, f z ≠ 0 → U ≤ (idealSelectedProduct z : ℝ) ∧
      (idealSelectedProduct z : ℝ) ≤ V) (x : IdealSelectedLabels P)
    (hx : idealCharacterCellApply P Q h ξ f x ≠ 0) :
    U*Real.exp (-h) < (idealSelectedProduct x : ℝ) ∧
      (idealSelectedProduct x : ℝ) < V*Real.exp h := by
  have hxpos : 0 < (idealSelectedProduct x : ℝ) := by exact_mod_cast idealSelectedProduct_pos hP x
  have hl := idealCharacterCellApply_log_support P Q hh f (a := Real.log U) (b := Real.log V)
    (fun z hz => by
      have hp : 0 < (idealSelectedProduct z : ℝ) := by exact_mod_cast idealSelectedProduct_pos hP z
      exact ⟨Real.log_le_log hU (hf z hz).1, Real.log_le_log hp (hf z hz).2⟩) x hx
  constructor
  · have hh := Real.exp_lt_exp.mpr hl.1
    simpa only [Real.exp_sub, Real.exp_log hU, Real.exp_log hxpos, Real.exp_neg, div_eq_mul_inv] using hh
  · have hh := Real.exp_lt_exp.mpr hl.2
    simpa only [Real.exp_add, Real.exp_log hV, Real.exp_log hxpos] using hh

end
end ArtinMatthews
