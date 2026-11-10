module

public import ArtinMatthews.SpectralAmbientTestPairing
public import ArtinMatthews.SpectralDecayingPoincare
public import ArtinMatthews.SpectralKLCompactOrder
public import ArtinMatthews.SpectralComplexNativeProfile
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralNativeEigenOrder
public import ArtinMatthews.SpectralNativePhysicalTransform
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

/-! An actual inverse profile determines the full native energy action.
The conversion retains the source width and the closed order strip. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0Primitive_physical_window_action (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (Y : ℝ) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y)
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ)))
    (hzero : ∀ x : ℝ, x ≤ 0 → F x = 0)
    (hreal : ∀ x : ℝ, 0 < x → star (F x) = F x)
    (C : ℝ) (hC : 0 ≤ C)
    (hsmall : ∀ x : ℝ, 0 < x → ‖F x‖ ≤ C*x^(3/4 : ℝ))
    (hlarge : ∀ x : ℝ, 1 ≤ x → ‖F x‖ ≤ C/x^2)
    (W : ℂ → ℂ) (h : SpectralEnergyTest)
    (hr : ∀ l, star (h l) = h l)
    (he : ∀ l : Ici (0 : ℝ),
      W ((-Complex.I)*Complex.sqrt (1/4-((l : ℝ) : ℂ))) = h l)
    (ht : ∀ t : ℝ, W (t : ℂ) = spectralContinuousTestSymbol h t)
    (htransform : ∀ ν : ℂ, |ν.re| ≤ 1/2 →
      spectralKLCompactOrderTransform F ν = W ((-Complex.I)*ν)*
        spectralKLCompactOrderTransform
          (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
            (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))) ν) :
    ∃ P : SpectralDecayingHeightProfile,
      P.exponent = 5/4 ∧
      (∀ y : ℝ, P.value y = Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
        (F ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re) ∧
      (∀ x : ℝ, 0 < x → spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
        (fun y => P.value ((gamma0CuspTrueWidth N r : ℝ)*y)) x = F x) ∧
      gamma0PrimitiveDecayingPoincare N r n P =
        gamma0AmbientTestOperator N h (gamma0PrimitiveFourierPoincareTest N r n ρ hρ hcρ hpρ) := by
  have hq : 0 < |cuspFourierFrequency 1 n| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hw : 0 < (gamma0CuspTrueWidth N r : ℝ) :=
    Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  obtain ⟨P,hP,hvalue,hphysical⟩ :=
    spectralComplexProfile_native_exists hq hw hC F hF hreal hsmall hlarge
  refine ⟨P,hP,hvalue,hphysical,?_⟩
  apply gamma0Primitive_order_multiplier_identification N r n hn Y hY ρ hρ hcρ hpρ hsρ P h hr
  · intro l
    rw [gamma0NativeOrderTransform_eq_physical N r n P.value F hzero hphysical,
      gamma0NativeOrderTransform_eq_compactOrder N r n hn]
    rw [htransform _ (spectralNonnegativeEnergy_order_abs_re_le l l.property),he l]
  · intro t
    rw [gamma0NativeOrderTransform_eq_physical N r n P.value F hzero hphysical,
      gamma0NativeOrderTransform_eq_compactOrder N r n hn]
    rw [htransform _ (by simp)]
    have hi : (-Complex.I)*((t : ℂ)*Complex.I) = (t : ℂ) := by
      calc
        _ = (t : ℂ)*(-(Complex.I^2)) := by ring
        _ = (t : ℂ) := by rw [Complex.I_sq]; ring
    rw [hi,ht t]

end ArtinMatthews
