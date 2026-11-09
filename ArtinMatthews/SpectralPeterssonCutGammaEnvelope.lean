module

public import ArtinMatthews.SpectralPeterssonStripIntegrable
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals


set_option backward.privateInPublic true
@[expose] public section

/-! The positive-height cut makes the Petersson Gamma envelope integrable
at weight two as well as every higher weight. -/
noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralPeterssonCutGammaEnvelope_integrable (k : ℕ) (hk : 2 ≤ k)
    (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) :
    IntegrableOn (fun y : ℝ => y^((k : ℝ)/2-2)*Real.exp (-(r*y))) (Ioi δ) := by
  by_cases hk3 : 3 ≤ k
  · have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    have hi := spectralPetersson_gammaEnvelope_integrable ((k : ℝ)/2-1) r (by linarith) hr
    have he : (k : ℝ)/2-1-1 = (k : ℝ)/2-2 := by ring
    rw [he] at hi
    exact hi.mono_set (Ioi_subset_Ioi hδ.le)
  · have hk2 : k = 2 := by omega
    subst k
    have hexp : IntegrableOn (fun y : ℝ => Real.exp (-(r*y))) (Ioi δ) := by
      simpa only [neg_mul] using integrableOn_exp_mul_Ioi (a := -r) (by linarith) δ
    have hbase := hexp.const_mul δ⁻¹
    apply hbase.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hδ.trans hy
    norm_num only [Nat.cast_ofNat,show (2 : ℝ)/2-2 = -1 by norm_num,Real.rpow_neg_one]
    rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr hy0.le) (Real.exp_nonneg _))]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hδ hy.le) (Real.exp_nonneg _)

end ArtinMatthews
