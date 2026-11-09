module

public import ArtinMatthews.SpectralCuspEulerOrigin


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Filter
noncomputable section

theorem cuspEuler_root_bounds : 1/2 ≤ cuspEulerPlus ∧ cuspEulerMinus < 1/2 ∧
    1-2*cuspEulerMinus = Real.sqrt 5 := by
  have hs : 0 < Real.sqrt (5:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  dsimp [cuspEulerPlus,cuspEulerMinus]
  constructor
  · linarith
  constructor
  · linarith
  · ring

/-- Genuine Euler uniqueness from actual weighted tail integrability and a
near-zero mass exponent strictly smaller than sqrt(5). The equation is
assumed in classical derivative form; no regularity upgrade is asserted here. -/
theorem cuspEuler_vanishes_of_energy_bounds (c c' : ℝ → ℂ)
    (hc : ∀ y>0, HasDerivAt c (c' y) y)
    (hc' : ∀ y>0, HasDerivAt c' (c y/(y:ℂ)^2) y)
    (htail : IntegrableOn (fun y : ℝ => ‖c y‖^2/y^2) (Ioi 1))
    {k C : ℝ} (hk : 0 ≤ k) (hk5 : k < Real.sqrt 5)
    (hnear : ∀ Y : ℝ, 0 < Y → Y ≤ 1 →
      (∫ y in Icc Y 1, ‖c y‖^2/y^2) ≤ C*Y^(-k)) :
    ∀ y>0, c y=0 := by
  obtain ⟨A,B,hsol⟩ := cuspEuler_solution_classification c c' hc hc'
  have htail' : IntegrableOn (fun y : ℝ =>
      ‖A*((y^cuspEulerPlus:ℝ):ℂ)+B*((y^cuspEulerMinus:ℝ):ℂ)‖^2/y^2) (Ioi 1) := by
    apply htail.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [hsol y (zero_lt_one.trans hy)]
  have hA := cuspEuler_tail_forces_plus_zero A B cuspEuler_root_bounds.1 cuspEuler_root_bounds.2.1 htail'
  subst A
  simp only [zero_mul,zero_add] at hsol
  have hnear' : ∀ Y : ℝ, 0 < Y → Y ≤ 1 →
      (∫ y in Icc Y 1, ‖B*((y^cuspEulerMinus:ℝ):ℂ)‖^2/y^2) ≤ C*Y^(-k) := by
    intro Y hY hY1
    have he : (∫ y in Icc Y 1, ‖B*((y^cuspEulerMinus:ℝ):ℂ)‖^2/y^2) =
        ∫ y in Icc Y 1, ‖c y‖^2/y^2 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      dsimp only
      rw [hsol y (hY.trans_le hy.1)]
    rw [he]
    exact hnear Y hY hY1
  have hq : k+2*cuspEulerMinus < 1 := by linarith [cuspEuler_root_bounds.2.2]
  have hB := cuspEuler_origin_forces_minus_zero B hk hq hnear'
  subst B
  intro y hy
  simpa only [zero_mul] using hsol y hy

end
end ArtinMatthews
