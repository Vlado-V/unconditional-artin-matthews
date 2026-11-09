module

public import ArtinMatthews.SpectralCuspUnitFourierMean
public import Mathlib.MeasureTheory.Integral.DominatedConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! Continuous dependence of the literal unit-width Fourier mean on
positive height. The averaging interval is fixed before integration. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0UnitCuspFourierMean_continuousOn (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (m : ℤ) (F : UpperHalfPlane → ℂ) (hF : Continuous F) :
    ContinuousOn (gamma0UnitCuspFourierMean N r m F) (Ioi (0 : ℝ)) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  let H (p : Ioi (0 : ℝ) × ℝ) : UpperHalfPlane :=
    gamma0EisensteinHorizontalPoint p.1.val p.1.property p.2
  have hH : Continuous H := by
    have hc : Continuous (fun p : Ioi (0 : ℝ) × ℝ => Complex.mk p.2 p.1.val) := by
      convert Complex.continuous_ofReal.comp continuous_snd |>.add
        ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul_const Complex.I) using 1
      funext p
      apply Complex.ext <;> simp
    exact hc.upperHalfPlaneMk (fun p => p.1.property)
  let U (y : Ioi (0 : ℝ)) (x : ℝ) :=
    cuspFourierPhase 1 m x * F (gamma0TrueCuspScaling N r • H (y,x))
  have hU : Continuous U.uncurry :=
    ((cuspFourierPhase_contDiff 1 m).continuous.comp continuous_snd).mul
      (hF.comp ((continuous_const_smul (gamma0TrueCuspScaling N r)).comp hH))
  have h : Continuous (fun y : Ioi (0 : ℝ) => ∫ x in (0 : ℝ)..1, U y x) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hU 0 1
  convert h using 1
  funext y
  exact dite_eq_left y.property

theorem gamma0UnitCuspFourierMean_raw_continuousOn (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (m : ℤ) (F : UpperHalfPlane → ℂ) (hF : Continuous F) :
    ContinuousOn (fun y => gamma0UnitCuspFourierMean N r m F
      (y/(gamma0CuspTrueWidth N r : ℝ))) (Ioi (0 : ℝ)) := by
  exact (gamma0UnitCuspFourierMean_continuousOn N r m F hF).comp
    (continuous_id.div_const _).continuousOn
    (fun y hy => show 0 < y/(gamma0CuspTrueWidth N r : ℝ) from
      div_pos (show 0 < y from hy) (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)))

end ArtinMatthews

