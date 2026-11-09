module

public import ArtinMatthews.CubicThetaLattice
public import Mathlib.Analysis.Asymptotics.Lemmas


set_option backward.privateInPublic true
@[expose] public section

/-!
# The vertical approach to the zero cusp

The actual lattice functional equation proves decay of the weight-one
normalized theta series along the imaginary axis at the zero cusp. This is a
necessary boundary estimate; it does not replace the full modular law or
uniform vanishing at every cusp.
-/
noncomputable section
open scoped Topology
open OAI OAI.SevenEighths Filter Complex UpperHalfPlane

namespace ArtinMatthews
open HeckeFamily

/-- Nonprincipal residue characters give a strong actual lattice FE pair. -/
theorem heckeTheta_pair_isStrong (χ : Character) (hχ : χ.residue ≠ 1) :
    IsStrongFEPair (HeckeTheta.pair (coefficients χ)) := by
  constructor
  · rw [HeckeTheta.pair_f₀, HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal χ hχ]
  · exact HeckeTheta.pair_g₀_eq_zero _ (HeckeCharacterAnalytic.coefficients_sum_eq_zero χ hχ)

/-- The actual dual lattice function tends to zero at positive infinity. -/
theorem tendsto_heckeTheta_dual_zero (χ : Character) (hχ : χ.residue ≠ 1) :
    Tendsto (HeckeTheta.pair (coefficients χ)).g atTop (𝓝 0) := by
  have h := (HeckeTheta.pair (coefficients χ)).hg_top (-1)
  rw [(heckeTheta_pair_isStrong χ hχ).hg₀] at h
  simp only [sub_zero] at h
  apply h.trans_tendsto
  simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 by norm_num))

/-- The vertical weight-one normalization at zero is exactly a rescaled dual
lattice theta value. -/
theorem heckeTheta_reciprocal_imaginary (χ : Character) (hχ : χ.residue ≠ 1)
    {y : ℝ} (hy : 0 < y) :
    heckeTheta χ ⟨((1 / y : ℝ) : ℂ) * Complex.I, by simpa using one_div_pos.mpr hy⟩ /
      (y : ℂ) = (HeckeTheta.pair (coefficients χ)).g (y / 2) / 12 := by
  rw [heckeTheta_eq_normalized_lattice χ hχ (one_div_pos.mpr hy),
    HeckeTheta.theta_eq_pair _ (by positivity)]
  have hfe := (HeckeTheta.pair (coefficients χ)).h_feq (y / 2) (by change 0 < y / 2; positivity)
  have hscale : 1 / (y / 2) = 2 * (1 / y) := by field_simp
  rw [hscale] at hfe
  simp only [HeckeTheta.pair_k, Real.rpow_one,
    show (HeckeTheta.pair (coefficients χ)).ε = 1 from rfl,
    one_mul, smul_eq_mul] at hfe
  rw [hfe]
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  push_cast
  field_simp
  ring

/-- Along the imaginary axis, the weight-one normalization at the zero cusp
tends to zero for a nonprincipal residue character. -/
theorem tendsto_heckeTheta_reciprocal_imaginary_zero (χ : Character)
    (hχ : χ.residue ≠ 1) :
    Tendsto (fun y : ℝ =>
      heckeTheta χ (UpperHalfPlane.ofComplex (((1 / y : ℝ) : ℂ) * Complex.I)) /
        (y : ℂ)) atTop (𝓝 0) := by
  have hg := (tendsto_heckeTheta_dual_zero χ hχ).comp
    (tendsto_id.atTop_div_const (show (0 : ℝ) < 2 by norm_num))
  have hh := hg.div_const (12 : ℂ)
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using one_div_pos.mpr hy)]
  exact (heckeTheta_reciprocal_imaginary χ hχ hy).symm

end ArtinMatthews
