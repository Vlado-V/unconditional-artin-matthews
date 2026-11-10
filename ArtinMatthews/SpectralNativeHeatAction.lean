module

public import ArtinMatthews.SpectralNativeHeatProfile
public import ArtinMatthews.SpectralABLHeatProfiles
public import ArtinMatthews.SpectralABLMultiplierReality
public import ArtinMatthews.SpectralABLOrderMultiplier
public import ArtinMatthews.SpectralAmbientMultiplierLinearity
public import ArtinMatthews.SpectralNativeEigenOrder
public import ArtinMatthews.SpectralNativePhysicalTransform
public import ArtinMatthews.SpectralTwoDecayingMultiplier
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

/-! Actual corrected-window action on the native Gaussian Poincare
test. The quarter normalization remains an explicit operator scalar. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0HeatPoincareTest_window_action (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (R : ℝ) (hR : 0 < R)
    (G : ℝ → ℂ) (hreg : SpectralKLHeatRegularity G)
    (hzero : ∀ x : ℝ, x ≤ 0 → G x = 0) (hreal : ∀ x, star (G x) = G x)
    (W : ℂ → ℂ) (h : SpectralEnergyTest) (hr : ∀ l, star (h l) = h l)
    (he : ∀ l : Ici (0 : ℝ), W ((-Complex.I)*Complex.sqrt (1/4-((l : ℝ) : ℂ))) = h l)
    (ht : ∀ t : ℝ, W (t : ℂ) = spectralContinuousTestSymbol h t)
    (htransform : ∀ ν : ℂ, |ν.re| ≤ 1/2 → spectralKLCompactOrderTransform G ν =
      W ((-Complex.I)*ν)*Complex.exp (ν^2/(R : ℂ)^2)) :
    ∃ Q : SpectralDecayingHeightProfile,
      Q.exponent = 5/4 ∧
      (∀ y : ℝ, Q.value y = Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
        (G ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re) ∧
      gamma0PrimitivePhysicalTest N r n Q.value = G ∧
      gamma0PrimitiveDecayingPoincare N r n Q = gamma0AmbientTestOperator N h
        (gamma0HeatPoincareTest N r n hn R hR) ∧
      gamma0AmbientTestOperator N ((1/4 : ℂ) • h) (gamma0HeatPoincareTest N r n hn R hR) =
        (1/4 : ℂ) • gamma0PrimitiveDecayingPoincare N r n Q := by
  obtain ⟨Q,hQ,hvalue,hphysical⟩ := gamma0HeatRegularity_native_exists N r n hn G hreg hzero hreal
  let P := gamma0HeatHeightProfile N r n hn R hR
  have hPcoef (ν : ℂ) : gamma0NativeOrderTransform N r n P.value ν =
      spectralKLCompactOrderTransform (spectralKLHeatProfile R) ν := by
    rw [gamma0NativeOrderTransform_eq_compactOrder N r n hn]
    change spectralKLCompactOrderTransform (gamma0PrimitivePhysicalTest N r n P.value) ν = _
    rw [show gamma0PrimitivePhysicalTest N r n P.value = spectralKLHeatProfile R from
      gamma0HeatHeightProfile_physical N r n hn R hR]
  have hQcoef (ν : ℂ) : gamma0NativeOrderTransform N r n Q.value ν =
      spectralKLCompactOrderTransform G ν := by
    rw [gamma0NativeOrderTransform_eq_compactOrder N r n hn]
    change spectralKLCompactOrderTransform (gamma0PrimitivePhysicalTest N r n Q.value) ν = _
    rw [hphysical]
  have hact : gamma0PrimitiveDecayingPoincare N r n Q = gamma0AmbientTestOperator N h
      (gamma0HeatPoincareTest N r n hn R hR) := by
    apply gamma0TwoDecayingPoincare_order_multiplier_identification N r n hn P Q h hr
    · intro l
      have hb := spectralNonnegativeEnergy_order_abs_re_le l l.property
      rw [hQcoef,hPcoef,htransform _ hb,spectralKLHeatProfile_continued_transform R hR _ hb,he l]
    · intro t
      rw [hQcoef,hPcoef,htransform _ (by simp),
        spectralKLHeatProfile_continued_transform R hR _ (by simp)]
      have hi : (-Complex.I)*((t : ℂ)*Complex.I) = (t : ℂ) := by
        calc
          _ = (t : ℂ)*(-(Complex.I^2)) := by ring
          _ = (t : ℂ) := by rw [Complex.I_sq]; ring
      rw [hi,ht t]
  refine ⟨Q,hQ,hvalue,hphysical,hact,?_⟩
  rw [gamma0AmbientTestOperator_smul,← hact]

theorem gamma0HeatPoincareTest_regular_action (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (T ε R : ℝ) (hT : 0 < T) (hR : 0 < R) :
    let G := spectralABLRegularHeatProfile T ε R
    ∃ Q : SpectralDecayingHeightProfile,
      Q.exponent = 5/4 ∧
      (∀ y : ℝ, Q.value y = Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
        (G ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re) ∧
      gamma0PrimitivePhysicalTest N r n Q.value = G ∧
      gamma0PrimitiveDecayingPoincare N r n Q = gamma0AmbientTestOperator N
        (spectralABLRegularEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _))
        (gamma0HeatPoincareTest N r n hn R hR) ∧
      gamma0AmbientTestOperator N (spectralABLLiteralRegularEnergyTest T ε hT)
        (gamma0HeatPoincareTest N r n hn R hR) =
          (1/4 : ℂ) • gamma0PrimitiveDecayingPoincare N r n Q := by
  apply gamma0HeatPoincareTest_window_action N r n hn R hR _
    (spectralABLRegularHeatProfile_properties T ε R hT hR)
    (spectralABLRegularHeatProfile_nonpositive_zero T ε R)
    (spectralABLRegularHeatProfile_real T ε R)
    (spectralABLRegularCorrected T (T^(1-ε)))
    (spectralABLRegularEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _))
    (spectralABLRegularEnergyTest_real _ _ _ _)
    (fun l => (spectralABLRegularEnergyTest_order _ _ _ _ l).symm)
  · intro t
    rw [spectralABLRegularCorrected_real,spectralABLRegularEnergyTest_continuous_symbol]
  · exact spectralABLRegularHeatProfile_continued_transform T ε R hT hR

theorem gamma0HeatPoincareTest_exceptional_action (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (a : ℝ) (A : ℕ) (R : ℝ) (hA : 1 ≤ A) (hR : 0 < R) :
    let G := spectralABLExceptionalHeatProfile a A R
    ∃ Q : SpectralDecayingHeightProfile,
      Q.exponent = 5/4 ∧
      (∀ y : ℝ, Q.value y = Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
        (G ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re) ∧
      gamma0PrimitivePhysicalTest N r n Q.value = G ∧
      gamma0PrimitiveDecayingPoincare N r n Q = gamma0AmbientTestOperator N (spectralABLExceptionalEnergyTest a A hA)
        (gamma0HeatPoincareTest N r n hn R hR) ∧
      gamma0AmbientTestOperator N (spectralABLLiteralExceptionalEnergyTest a A hA)
        (gamma0HeatPoincareTest N r n hn R hR) =
          (1/4 : ℂ) • gamma0PrimitiveDecayingPoincare N r n Q := by
  apply gamma0HeatPoincareTest_window_action N r n hn R hR _
    (spectralABLExceptionalHeatProfile_properties a A R hA hR)
    (spectralABLExceptionalHeatProfile_nonpositive_zero a A R)
    (spectralABLExceptionalHeatProfile_real a A R)
    (spectralABLExceptionalCorrected a A) (spectralABLExceptionalEnergyTest a A hA)
    (spectralABLExceptionalEnergyTest_real _ _ _)
    (fun l => (spectralABLExceptionalEnergyTest_order _ _ _ l).symm)
  · intro t
    rw [spectralABLExceptionalCorrected_real,spectralABLExceptionalEnergyTest_continuous_symbol]
  · exact spectralABLExceptionalHeatProfile_continued_transform a A R hA hR

end ArtinMatthews
