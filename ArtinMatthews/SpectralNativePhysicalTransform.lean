module

public import ArtinMatthews.SpectralNativeMultiplierIdentification
public import ArtinMatthews.SpectralKLCompactOrder
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
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

/-! The actual native height coefficient is the literal physical
K transform, with its positive-height support retained. -/

noncomputable section
open Set MeasureTheory OAI.CubicEisenstein
open scoped MatrixGroups
namespace ArtinMatthews

theorem spectralKLHeightPhysicalTest_nonpos {q : ℝ} (hq : 0 < q)
    (ρ : ℝ → ℝ) {x : ℝ} (hx : x ≤ 0) :
    spectralKLHeightPhysicalTest q ρ x = 0 := by
  have hs : Real.sqrt (x/q) = 0 :=
    Real.sqrt_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx hq.le)
  simp [spectralKLHeightPhysicalTest,spectralKLHeightBaseTest,hs]

theorem gamma0NativeOrderTransform_eq_physical (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (ρ : ℝ → ℝ) (F : ℝ → ℂ)
    (hzero : ∀ x : ℝ, x ≤ 0 → F x = 0)
    (hphysical : ∀ x : ℝ, 0 < x →
      spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
        (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y)) x = F x) (ν : ℂ) :
    gamma0NativeOrderTransform N r n ρ ν = spectralKLCompactOrderTransform F ν := by
  symm
  unfold spectralKLCompactOrderTransform
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ))
    (fun x hx => ?_)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [spectralKLCompactOrderIntegrand,spectralKLPhysicalCompactDiv]
    rw [hphysical x hx]
  · simp [spectralKLCompactOrderIntegrand,spectralKLPhysicalCompactDiv,
      hzero x (le_of_not_gt hx)]

theorem gamma0NativeOrderTransform_eq_compactOrder (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (ρ : ℝ → ℝ) (ν : ℂ) :
    gamma0NativeOrderTransform N r n ρ ν = spectralKLCompactOrderTransform
      (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
        (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))) ν := by
  apply gamma0NativeOrderTransform_eq_physical
  · exact fun x hx => spectralKLHeightPhysicalTest_nonpos
      (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)) _ hx
  · exact fun _ _ => rfl

end ArtinMatthews
