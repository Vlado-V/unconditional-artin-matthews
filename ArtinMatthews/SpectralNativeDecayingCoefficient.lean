module

public import ArtinMatthews.SpectralAmbientBesselAmplitude
public import ArtinMatthews.SpectralDecayingPoincare
public import ArtinMatthews.SpectralDecayingPhysicalPairing
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralNativeEigenOrder
public import ArtinMatthews.SpectralNativeOrderCutoff
public import ArtinMatthews.SpectralNativeOrderTransform
public import ArtinMatthews.SpectralTrueWidthPhysicalProfile
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

/-! The actual noncompact Poincare vector has the literal K-integral
coefficient against every ambient eigenvector, including residual modes. -/

noncomputable section
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped Topology MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0PrimitiveDecayingPoincare_ambient_order_integral (N : ℕ) [NeZero N]
    (eig : ℝ) (heig : 0 ≤ eig) (v : Gamma0RegionL2 N)
    (hG : gamma0Green N v = (((eig+1)⁻¹ : ℝ) : ℂ) • v)
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (P : SpectralDecayingHeightProfile) :
    inner ℂ (gamma0PrimitiveDecayingPoincare N r n P) v =
      (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)*
        gamma0AmbientBesselAmplitude N eig heig v hG r
          ((gamma0CuspFrequencyStep N r : ℤ)*n) (gamma0CuspFrequencyStep_mul_ne_zero N r hn)*
        (∫ x in Ioi (0 : ℝ), schlafliBesselK (Complex.sqrt (1/4-(eig : ℂ))) x*
          (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
            (fun y => P.value ((gamma0CuspTrueWidth N r : ℝ)*y)) x/(x : ℂ))) := by
  let q := |cuspFourierFrequency 1 n|
  let w := (gamma0CuspTrueWidth N r : ℝ)
  let ν := Complex.sqrt (1/4-(eig : ℂ))
  let f := spectralKLHeightPhysicalTest q (fun y => P.value (w*y))
  let A : ℂ := (Real.sqrt w : ℂ)*gamma0AmbientBesselAmplitude N eig heig v hG r
    ((gamma0CuspFrequencyStep N r : ℤ)*n) (gamma0CuspFrequencyStep_mul_ne_zero N r hn)
  let H (K : ℕ) := gamma0PrimitiveFourierPoincareTest N r n
    (spectralHeightProfilePartial K P.value)
    (spectralHeightProfilePartial_contDiff K P.value P.smooth)
    (spectralHeightProfilePartial_compact K P.value)
    (spectralHeightProfilePartial_positive K P.value)
  have hq : 0 < q := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hf : Measurable f := spectralKLHeightPhysicalTest_width_measurable hq hw P.value P.smooth.continuousOn
  have hp : ∀ x, 0 < x → ‖f x‖ ≤
      (P.bound*w^P.exponent/q^(P.exponent-1/2))*x^(P.exponent-1/2) :=
    fun _ hx => spectralKLHeightPhysicalTest_decaying_power hq hw P hx
  have hPb := P.bound_nonneg
  have hright := (spectralKLPower_order_cutoff_tendsto f hf (div_pos hw hq)
    (by positivity : 0 ≤ P.bound*w^P.exponent/q^(P.exponent-1/2))
    (by norm_num : (0 : ℝ) ≤ 1/2)
    (by linarith [P.exponent_gt_one] : 1/2 < P.exponent-1/2) hp ν
    (spectralNonnegativeEnergy_order_abs_re_le eig heig)).const_mul A
  have hleft : Tendsto (fun K : ℕ => inner ℂ (H K) v) atTop
      (𝓝 (inner ℂ (gamma0PrimitiveDecayingPoincare N r n P) v)) :=
    ((continuous_id.inner continuous_const).tendsto _).comp
      (gamma0PrimitiveDecayingPoincare_partial_tendsto N r n P)
  have hstep (K : ℕ) : inner ℂ (H K) v =
      A*(∫ x in Ioi (0 : ℝ), schlafliBesselK ν x*
        (spectralWeylProfileCutoff (w/q) K f x/(x : ℂ))) := by
    let Y : ℝ := ((2 : ℝ)^(K+1))⁻¹/2
    have hY : 0 < Y := by dsimp only [Y]; positivity
    have hs : tsupport (spectralHeightProfilePartial K P.value) ⊆ Ioi Y := by
      intro y hy
      have hy' := (spectralHeightProfilePartial_tsupport K P.value hy).1
      have hpos : 0 < ((2 : ℝ)^(K+1))⁻¹ := by positivity
      exact (half_lt_self hpos).trans_le hy'
    have h := gamma0PrimitiveFourierPoincareTest_ambient_order_integral N eig heig v hG r n hn
      Y hY (spectralHeightProfilePartial K P.value)
      (spectralHeightProfilePartial_contDiff K P.value P.smooth)
      (spectralHeightProfilePartial_compact K P.value)
      (spectralHeightProfilePartial_positive K P.value) hs
    simp_rw [spectralKLHeightPhysicalTest_partial_width] at h
    exact h
  rw [funext hstep] at hleft
  exact tendsto_nhds_unique hleft hright

end ArtinMatthews
