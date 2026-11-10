module

public import ArtinMatthews.SpectralWeylSpectralGaussianIntegrable
public import ArtinMatthews.SpectralBesselKEquation
public import ArtinMatthews.SpectralKLAnalysisProductWeight
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual J/K spectral bilinear forms are continuous at every
positive modulus.  The local dominated-convergence bound retains the
proved spectral-edge weight and uses the genuine positive-argument kernels. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology

namespace ArtinMatthews

def spectralWeylSpectralBilinear (M : ℝ → ℝ → ℂ) (F G : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∫ r : ℝ, M r X*F r*star (G r) ∂spectralKLSpectralMeasure

theorem spectralWeylJMultiplier_continuousOn (r : ℝ) :
    ContinuousOn (spectralWeylJMultiplier r) (Ioi (0 : ℝ)) := by
  have hJ (ν : ℂ) : ContinuousOn (fun X : ℝ => Complex.besselJ ν (X : ℂ)) (Ioi (0 : ℝ)) := by
    intro X hX
    exact ((Complex.analyticAt_besselJ ν (Complex.ofReal_mem_slitPlane.mpr hX)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  let c : ℂ := (2*(Real.pi : ℂ)*Complex.I)/(Real.sinh (Real.pi*r) : ℂ)
  let ν₁ : ℂ := (((2*r : ℝ) : ℂ)*Complex.I)
  let ν₂ : ℂ := (((-2*r : ℝ) : ℂ)*Complex.I)
  have hc : ContinuousOn (fun X : ℝ => c*(Complex.besselJ ν₁ (X : ℂ)-Complex.besselJ ν₂ (X : ℂ))/(X : ℂ))
      (Ioi (0 : ℝ)) :=
    (((hJ ν₁).sub (hJ ν₂)).const_mul c).div Complex.continuous_ofReal.continuousOn
      (fun X hX => Complex.ofReal_ne_zero.mpr (show 0 < X from hX).ne')
  apply hc.congr
  intro X hX
  rw [spectralWeylJMultiplier,ite_eq_left (show 0 < X from hX)]

theorem spectralWeylKMultiplier_continuousOn (r : ℝ) :
    ContinuousOn (spectralWeylKMultiplier r) (Ioi (0 : ℝ)) := by
  have hK : ContinuousOn (schlafliBesselK (((2*r : ℝ) : ℂ)*Complex.I)) (Ioi (0 : ℝ)) := by
    intro X hX
    exact (schlafliBesselK_hasDerivAt _ _ hX).continuousAt.continuousWithinAt
  let c : ℂ := 8*(Real.cosh (Real.pi*r) : ℂ)
  have hc : ContinuousOn (fun X : ℝ => c*schlafliBesselK (((2*r : ℝ) : ℂ)*Complex.I) X/(X : ℂ))
      (Ioi (0 : ℝ)) :=
    (hK.const_mul c).div Complex.continuous_ofReal.continuousOn
      (fun X hX => Complex.ofReal_ne_zero.mpr (show 0 < X from hX).ne')
  apply hc.congr
  intro X hX
  rw [spectralWeylKMultiplier,ite_eq_left (show 0 < X from hX)]

theorem spectralWeylSpectralBilinear_continuousOn (M : ℝ → ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (F G : ℝ → ℂ) (hcF : Continuous F) (hcG : Continuous G)
    (hF : MemLp F 2 spectralKLSpectralMeasure) (hG : MemLp G 2 spectralKLSpectralMeasure)
    (hM : Measurable (fun q : ℝ × ℝ => M q.1 q.2))
    (hMc : ∀ r : ℝ, 0 < r → ContinuousOn (M r) (Ioi (0 : ℝ)))
    (hMb : ∀ r X : ℝ, 0 < r → 0 < X →
      ‖(X : ℂ)*M r X‖ ≤ 4*Real.pi*Real.exp (X^2/4)*(1+C/r)) :
    ContinuousOn (spectralWeylSpectralBilinear M F G) (Ioi (0 : ℝ)) := by
  intro X₀ hX₀
  change 0 < X₀ at hX₀
  let A (X r : ℝ) : ℂ := ((X : ℂ)*M r X)*F r*star (G r)
  let B : ℝ := 4*Real.pi*Real.exp ((X₀+1)^2/4)
  let W (r : ℝ) : ℝ := ‖F r‖*‖G r‖*(1+C/r)
  have hW : Integrable W spectralKLSpectralMeasure :=
    spectralKL_continuous_L2_product_order_weight_integrable F G hcF hcG hF hG C
  have ha : ContinuousAt (fun X : ℝ => ∫ r : ℝ, A X r ∂spectralKLSpectralMeasure) X₀ := by
    apply continuousAt_of_dominated (bound := fun r => B*W r)
    · filter_upwards with X
      have hm : Measurable (fun r : ℝ => M r X) := hM.comp (measurable_id.prodMk measurable_const)
      exact (((measurable_const.mul hm).mul hcF.measurable).mul
        (continuous_star.measurable.comp hcG.measurable)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhds hX₀ (lt_add_of_pos_right X₀ zero_lt_one)] with X hX
      filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hr
      have hB : 4*Real.pi*Real.exp (X^2/4) ≤ B := by
        dsimp [B]
        gcongr
        · exact hX.1.le
        · exact hX.2.le
      have hW0 : 0 ≤ 1+C/r := by positivity
      have hm := (hMb r X hr hX.1).trans (mul_le_mul_of_nonneg_right hB hW0)
      dsimp [A,W]
      rw [norm_mul,norm_mul]
      change ‖(X : ℂ)*M r X‖*‖F r‖*‖star (G r)‖ ≤ _
      rw [norm_star]
      calc
        _ ≤ (B*(1+C/r))*‖F r‖*‖G r‖ := by gcongr
        _ = _ := by ring_nf
    · exact hW.const_mul B
    · filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hr
      have hc := (hMc r hr X₀ hX₀).continuousAt (Ioi_mem_nhds hX₀)
      exact ((Complex.continuous_ofReal.continuousAt.mul hc).mul continuousAt_const).mul continuousAt_const
  have he (X : ℝ) : (∫ r : ℝ, A X r ∂spectralKLSpectralMeasure) =
      (X : ℂ)*spectralWeylSpectralBilinear M F G X := by
    rw [spectralWeylSpectralBilinear,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    dsimp only [A]
    ring_nf
  have hl : (fun X : ℝ => (∫ r : ℝ, A X r ∂spectralKLSpectralMeasure)/(X : ℂ))
      =ᶠ[𝓝 X₀] spectralWeylSpectralBilinear M F G := by
    filter_upwards [Ioi_mem_nhds hX₀] with X hX
    rw [he]
    field_simp [Complex.ofReal_ne_zero.mpr (show 0 < X from hX).ne']
  exact ((ha.div Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr hX₀.ne')).congr hl).continuousWithinAt

theorem spectralWeylSpectralBilinear_gaussian_integrable (M : ℝ → ℝ → ℂ) (p : ℝ) (F G : ℝ → ℂ)
    (hi : Integrable (spectralWeylGaussianSpectralIntegrand M p F G)
      ((volume.restrict (Ioi (0 : ℝ))).prod spectralKLSpectralMeasure)) :
    IntegrableOn (fun X : ℝ => Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      spectralWeylSpectralBilinear M F G X) (Ioi (0 : ℝ)) := by
  apply hi.integral_prod_left.congr
  filter_upwards with X
  rw [spectralWeylSpectralBilinear,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  unfold spectralWeylGaussianSpectralIntegrand
  ring_nf

end ArtinMatthews
