module

public import ArtinMatthews.SpectralNativeMultiplierIdentification
public import ArtinMatthews.SpectralNativeDecayingCoefficient
public import ArtinMatthews.SpectralNativeDecayingContinuous
public import ArtinMatthews.SpectralNativeMultiplierUniqueness
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

/-! The full native multiplier is identified between two actual
noncompact Poincare vectors by their proved spectral coefficients. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0TwoDecayingPoincare_order_multiplier_identification (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0)
    (P Q : SpectralDecayingHeightProfile) (h : SpectralEnergyTest)
    (hreal : ∀ l, star (h l) = h l)
    (hatomic : ∀ l : Ici (0 : ℝ),
      gamma0NativeOrderTransform N r n Q.value (Complex.sqrt (1/4-((l : ℝ) : ℂ))) =
        h l*gamma0NativeOrderTransform N r n P.value (Complex.sqrt (1/4-((l : ℝ) : ℂ))))
    (hcontinuous : ∀ t : ℝ,
      gamma0NativeOrderTransform N r n Q.value ((t : ℂ)*Complex.I) =
        spectralContinuousTestSymbol h t*gamma0NativeOrderTransform N r n P.value ((t : ℂ)*Complex.I)) :
    gamma0PrimitiveDecayingPoincare N r n Q =
      gamma0AmbientTestOperator N h (gamma0PrimitiveDecayingPoincare N r n P) := by
  let u := gamma0PrimitiveDecayingPoincare N r n P
  let w := gamma0PrimitiveDecayingPoincare N r n Q
  have heigen (l : Ici (0 : ℝ)) (v : Gamma0RegionL2 N)
      (hG : gamma0Green N v = ((((l : ℝ)+1)⁻¹ : ℝ) : ℂ) • v) :
      inner ℂ v w = h l*inner ℂ v u := by
    let A := (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)*
      gamma0AmbientBesselAmplitude N l l.property v hG r
        ((gamma0CuspFrequencyStep N r : ℤ)*n) (gamma0CuspFrequencyStep_mul_ne_zero N r hn)
    have hw := gamma0PrimitiveDecayingPoincare_ambient_order_integral N l l.property v hG r n hn Q
    have hu := gamma0PrimitiveDecayingPoincare_ambient_order_integral N l l.property v hG r n hn P
    change inner ℂ w v = A*gamma0NativeOrderTransform N r n Q.value
      (Complex.sqrt (1/4-((l : ℝ) : ℂ))) at hw
    change inner ℂ u v = A*gamma0NativeOrderTransform N r n P.value
      (Complex.sqrt (1/4-((l : ℝ) : ℂ))) at hu
    have he : inner ℂ w v = h l*inner ℂ u v := by
      rw [hw,hu,hatomic l]
      ring
    have hs := congrArg star he
    change (starRingEnd ℂ) (inner ℂ w v) =
      (starRingEnd ℂ) (h l*inner ℂ u v) at hs
    rw [map_mul,inner_conj_symm,inner_conj_symm] at hs
    have hr : (starRingEnd ℂ) (h l) = h l := hreal l
    rwa [hr] at hs
  apply gamma0AmbientTestOperator_eq_of_spectral_data N h u w
  · intro i
    let l : Ici (0 : ℝ) := ⟨gamma0AllHeightGradientSpectralValue N i,
      gamma0AllHeightGradientSpectralValue_nonneg N i⟩
    have hG : gamma0Green N (gamma0FullCuspidalSpectralBasis N i).val =
        ((((l : ℝ)+1)⁻¹ : ℝ) : ℂ) • (gamma0FullCuspidalSpectralBasis N i).val := by
      simpa only [l,gamma0AllHeightGradientSpectralValue,sub_add_cancel,inv_inv,
        gamma0AllHeightSpectralValue_real] using gamma0FullCuspidalSpectralBasis_eigen N i
    exact heigen l (gamma0FullCuspidalSpectralBasis N i).val hG
  · apply PiLp.ext
    intro i
    rw [gamma0EisensteinTestMultiplier_apply]
    apply Lp.ext
    filter_upwards [gamma0PrimitiveDecayingPoincare_continuous_ae N r n hn 1 zero_lt_one Q i,
      gamma0PrimitiveDecayingPoincare_continuous_ae N r n hn 1 zero_lt_one P i,
      spectralLpTestMultiplier_ae gamma0EisensteinSpectralMeasure (spectralContinuousTestSymbol h)
        ((gamma0EisensteinAnalysis N u) i)] with t hnew hold hmul
    change (gamma0EisensteinAnalysis N w) i t =
      spectralLpTestMultiplier gamma0EisensteinSpectralMeasure (spectralContinuousTestSymbol h)
        ((gamma0EisensteinAnalysis N u) i) t
    rw [hmul,hnew,hold]
    change star (_*gamma0NativeOrderTransform N r n Q.value ((t : ℂ)*Complex.I)) =
      spectralContinuousTestSymbol h t*star (_*gamma0NativeOrderTransform N r n P.value ((t : ℂ)*Complex.I))
    have hr : star (spectralContinuousTestSymbol h t) = spectralContinuousTestSymbol h t :=
      hreal (spectralContinuousEnergyParameter t)
    rw [hcontinuous t]
    simp only [star_mul,hr]
    ring
  · intro l _ j
    exact heigen l (gamma0ResidualEigenbasis N l j).val (gamma0ResidualEigenbasis_green N l j)

end ArtinMatthews
