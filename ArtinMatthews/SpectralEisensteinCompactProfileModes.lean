module

public import ArtinMatthews.SpectralCuspConstantTermOperator
public import ArtinMatthews.SpectralCuspEisensteinEquivalentWidths
public import ArtinMatthews.SpectralEisensteinCompactProfile
public import ArtinMatthews.SpectralCuspConstantTermHeights
public import ArtinMatthews.SpectralCuspContinuousMean
public import ArtinMatthews.SpectralEisensteinHighProfiles
public import ArtinMatthews.SpectralEisensteinProfileMajorants
public import ArtinMatthews.SpectralEisensteinRestrictionIdentification
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact literal high cusp means for arbitrary compact height profiles.
This identifies the upper cutoff at critical parameters in the native
completed constant-term Hilbert space. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0CuspCompactHeightProfile_constant_mode (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hpos : tsupport ρ⊆Ioi (0:ℝ)) (hlow : ∀ t≤1,ρ t=0)
    (Y : ℝ) (hY : 0<Y) (hhigh : (gamma0CuspTrueWidth N r:ℝ)≤Y) :
    gamma0CuspConstantTerm N r Y hY (gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N a ρ hρ hρc hpos))
      =ᵐ[(cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure Y]
      fun y => gamma0CuspEisensteinIndicator N r a*ρ (y/(gamma0CuspTrueWidth N r:ℝ)) := by
  let F : UpperHalfPlane → ℂ := fun z => gamma0CuspHeightProfile N a ρ (r⁻¹ • z)
  have hF : Continuous F := (gamma0CuspHeightProfile_continuous_of_zero_low N a ρ hρ.continuous
    zero_lt_one hlow).comp (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹))
  have hw : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  have hc := cuspHyperbolicConstantTerm_continuous_representative (N:ℝ) Y hw hY
    (gamma0CuspMassRestriction N r Y hY
      (gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N a ρ hρ hρc hpos)))
    F hF (gamma0CuspHeightProfileEnergy_restriction_ae N r a ρ hρ hρc hpos Y hY)
  filter_upwards [Measure.ae_smul_measure hc (cuspHorizontalMeasure (N:ℝ) univ),
    cuspWeightedVerticalMeasure_ae_gt (N:ℝ) Y hY] with y hy hyY
  change (gamma0CuspConstantTerm N r Y hY
    (gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N a ρ hρ hρc hpos))) y=
    cuspHorizontalMean (N:ℝ) (cuspContinuousPlaneExtension Y hY F) y at hy
  rw [hy,cuspContinuousPlaneExtension_mean (N:ℝ) Y hw.le hY F y hyY]
  have he (x : ℝ) : F (gamma0EisensteinHorizontalPoint y (hY.trans hyY) x)=
      gamma0CuspEisensteinIndicator N r a*ρ (y/(gamma0CuspTrueWidth N r:ℝ)) :=
    gamma0CuspHeightProfile_raw_high N r a ρ hlow _ (hhigh.trans hyY.le)
  simp_rw [he]
  rw [intervalIntegral.integral_const,sub_zero,Complex.real_smul,Complex.ofReal_natCast,←mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast (NeZero.ne N)),one_mul]

end ArtinMatthews
