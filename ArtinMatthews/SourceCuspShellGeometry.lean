module

public import ArtinMatthews.SourceCuspShellGradient
public import Mathlib.Analysis.Calculus.LocalExtr.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The actual logarithmic cutoff is one on the middle dyadic shell and has
zero value and zero gradient outside its three-shell support. -/
namespace ArtinMatthews
open OAI.CubicEisenstein SourceHyperbolicGreen Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem sourceCuspShellBump_deriv_zero {t : ℝ} (ht : t ≤ 0 ∨ 3 * Real.log 2 ≤ t) :
    deriv sourceCuspShellBump t = 0 := by
  have hz : sourceCuspShellBump t = 0 := ht.elim sourceCuspShellBump_zero_left sourceCuspShellBump_zero_right
  have hmin : IsLocalMin sourceCuspShellBump t := by
    exact Filter.Eventually.of_forall (fun x => by rw [hz]; exact sourceCuspShellBump_nonneg x)
  exact hmin.deriv_eq_zero

theorem sourceProductShellCutoff_nonneg (C a : ℝ) (p : ProductSpace ι) :
    0 ≤ sourceProductShellCutoff C a p := sourceCuspShellBump_nonneg _

theorem sourceProductShellCutoff_le_one (C a : ℝ) (p : ProductSpace ι) :
    sourceProductShellCutoff C a p ≤ 1 := sourceCuspShellBump_le_one _

theorem sourceProductShellCutoff_one (C a : ℝ) (p : ProductSpace ι)
    (hlo : a + Real.log 2 ≤ sourceProductLogHeight C p)
    (hhi : sourceProductLogHeight C p ≤ a + 2 * Real.log 2) :
    sourceProductShellCutoff C a p = 1 :=
  sourceCuspShellBump_one (by linarith) (by linarith)

theorem sourceProductShellCutoff_zero (C a : ℝ) (p : ProductSpace ι)
    (h : sourceProductLogHeight C p ≤ a ∨ a + 3 * Real.log 2 ≤ sourceProductLogHeight C p) :
    sourceProductShellCutoff C a p = 0 := by
  rcases h with h | h
  · exact sourceCuspShellBump_zero_left (by linarith)
  · exact sourceCuspShellBump_zero_right (by linarith)

theorem sourceProductShellCutoff_energy_zero (C a : ℝ) (p : ProductSpace ι)
    (hp : p ∈ productUpper ι)
    (h : sourceProductLogHeight C p ≤ a ∨ a + 3 * Real.log 2 ≤ sourceProductLogHeight C p) :
    productGradientEnergy (fun q => (sourceProductShellCutoff C a q : ℂ)) p = 0 := by
  rw [sourceProductShellCutoff_energy C a p hp,
    sourceCuspShellBump_deriv_zero (h.imp (by intro h; linarith) (by intro h; linarith))]
  ring

private theorem log_two_mul (T : ℝ) (hT : 0 < T) :
    Real.log (2 * T) = Real.log T + Real.log 2 := by
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hT.ne']
  ring

private theorem log_four_mul (T : ℝ) (hT : 0 < T) :
    Real.log (4 * T) = Real.log T + 2 * Real.log 2 := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hT.ne', h4, Real.log_pow]
  ring

private theorem log_eight_mul (T : ℝ) (hT : 0 < T) :
    Real.log (8 * T) = Real.log T + 3 * Real.log 2 := by
  have h8 : (8 : ℝ) = 2 ^ 3 := by norm_num
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hT.ne', h8, Real.log_pow]
  ring

theorem sourceProductShellCutoff_middle (C T : ℝ) (hC : 0 < C) (hT : 0 < T)
    (p : ProductSpace ι) (hp : p ∈ productUpper ι)
    (hlo : 2 * T ≤ C * ∏ i, (p i 2) ^ 2)
    (hhi : C * ∏ i, (p i 2) ^ 2 ≤ 4 * T) :
    sourceProductShellCutoff C (Real.log T) p = 1 := by
  have hH : 0 < C * ∏ i, (p i 2) ^ 2 :=
    mul_pos hC (Finset.prod_pos (fun i _ => pow_pos (productUpper_pos hp i) _))
  apply sourceProductShellCutoff_one
  · rw [sourceProductLogHeight_eq C hC p hp, ← log_two_mul T hT]
    exact Real.log_le_log (by positivity) hlo
  · rw [sourceProductLogHeight_eq C hC p hp, ← log_four_mul T hT]
    exact Real.log_le_log hH hhi

theorem sourceProductShellCutoff_outside (C T : ℝ) (hC : 0 < C) (hT : 0 < T)
    (p : ProductSpace ι) (hp : p ∈ productUpper ι)
    (h : C * ∏ i, (p i 2) ^ 2 ≤ T ∨ 8 * T ≤ C * ∏ i, (p i 2) ^ 2) :
    sourceProductShellCutoff C (Real.log T) p = 0 ∧
      productGradientEnergy (fun q => (sourceProductShellCutoff C (Real.log T) q : ℂ)) p = 0 := by
  have hH : 0 < C * ∏ i, (p i 2) ^ 2 :=
    mul_pos hC (Finset.prod_pos (fun i _ => pow_pos (productUpper_pos hp i) _))
  have hlog : sourceProductLogHeight C p ≤ Real.log T ∨
      Real.log T + 3 * Real.log 2 ≤ sourceProductLogHeight C p := by
    rw [sourceProductLogHeight_eq C hC p hp, ← log_eight_mul T hT]
    exact h.imp (Real.log_le_log hH) (Real.log_le_log (by positivity))
  exact ⟨sourceProductShellCutoff_zero C _ p hlog, sourceProductShellCutoff_energy_zero C _ p hp hlog⟩

end
end ArtinMatthews
