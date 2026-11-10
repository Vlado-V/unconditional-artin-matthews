module

public import ArtinMatthews.SourceKPAdelicCutoffDefect
public import ArtinMatthews.SourceKPAdelicCutoffGenuine
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

/-! The literal Casimir and the compact cutoff defect preserve the
actual cubic central character. -/

namespace ArtinMatthews
open NumberField
open scoped NumberField BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchGlobalCasimir_left_covariant
    (f : SourceKPAdelicProjective K hζ → ℂ) (a : SourceKPAdelicProjective K hζ) (c : ℂ)
    (hf : ∀ q, f (a*q) = c*f q) (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    sourceArchGlobalCasimir K hζ f (a*q) v = c*sourceArchGlobalCasimir K hζ f q v := by
  have hU (z : ℂ) : sourceArchGlobalUpperTranslate K hζ f (a*q) v z =
      fun t => c*sourceArchGlobalUpperTranslate K hζ f q v z t := by
    funext t
    unfold sourceArchGlobalUpperTranslate
    rw [mul_assoc,hf]
  have hA : sourceArchGlobalDiagonalTranslate K hζ f (a*q) v =
      fun t => c*sourceArchGlobalDiagonalTranslate K hζ f q v t := by
    funext t
    unfold sourceArchGlobalDiagonalTranslate
    rw [mul_assoc,hf]
  unfold sourceArchGlobalCasimir
  rw [hU 1,hU Complex.I,hA]
  simp only [deriv_const_mul_field',deriv_const_mul_field]
  ring

theorem sourceKPAdelicCutoffCasimir_center (T : ℝ) (s : ℂ) (z : rootsOfUnity 3 K)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    sourceArchGlobalCasimir K hζ (sourceKPAdelicCutoffEisenstein K hζ T s)
      (sourceKPAdelicProjectiveCenter K hζ z*q) v =
        (sourceKPAdelicCentralComplex K hζ z : ℂ) *
          sourceArchGlobalCasimir K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) q v :=
  sourceArchGlobalCasimir_left_covariant K hζ _ _ _
    (sourceKPAdelicCutoffEisenstein_center K hζ T s z) q v

theorem sourceKPAdelicCutoffCasimirDefect_center (T : ℝ) (s : ℂ) (z : rootsOfUnity 3 K)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCutoffCasimirDefect K hζ T s (sourceKPAdelicProjectiveCenter K hζ z*q) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ)*sourceKPAdelicCutoffCasimirDefect K hζ T s q := by
  unfold sourceKPAdelicCutoffCasimirDefect
  simp_rw [sourceKPAdelicCutoffCasimir_center,sourceKPAdelicCutoffEisenstein_center]
  rw [← Finset.mul_sum]
  ring

end
end ArtinMatthews
