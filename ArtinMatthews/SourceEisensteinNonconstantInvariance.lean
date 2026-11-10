module

public import ArtinMatthews.SourceEisensteinNonconstant
public import ArtinMatthews.SourceKPAdelicKernelContinuity
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

/-! The actual compact and unipotent periods are retained by the nonconstant cusp remainder. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactEisenstein_deepCompact_right (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicCompactEisenstein K hζ s (g * k.val) = sourceKPAdelicCompactEisenstein K hζ s g := by
  unfold sourceKPAdelicCompactEisenstein sourceKPAdelicEisensteinSum
  apply tsum_congr
  intro c
  induction c using Quotient.inductionOn with
  | _ γ =>
    change sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveRationalLift K hζ γ * (g * k.val)) =
      sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveRationalLift K hζ γ * g)
    rw [← mul_assoc]
    exact sourceKPAdelicCompactScalar_right K hζ s _ k

theorem sourceKPAdelicTraceIntertwiner_deepCompact_right (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicTraceIntertwiner K hζ s (g * k.val) = sourceKPAdelicTraceIntertwiner K hζ s g := by
  unfold sourceKPAdelicTraceIntertwiner sourceKPAdelicIntertwiner
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  unfold sourceKPAdelicIntertwiningKernel
  rw [← mul_assoc]
  exact sourceKPAdelicCompactScalar_right K hζ s _ k

theorem sourceKPAdelicNonconstantEisenstein_deepCompact_right (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicNonconstantEisenstein K hζ s (g * k.val) = sourceKPAdelicNonconstantEisenstein K hζ s g := by
  rw [sourceKPAdelicNonconstantEisenstein, sourceKPAdelicNonconstantEisenstein,
    sourceKPAdelicCompactEisenstein_deepCompact_right, sourceKPAdelicCompactScalar_right,
    sourceKPAdelicTraceIntertwiner_deepCompact_right]

theorem sourceKPAdelicNonconstantEisenstein_upper_rational {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) (a : K) :
    sourceKPAdelicNonconstantEisenstein K hζ s
      (sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] a + y) * g) =
        sourceKPAdelicNonconstantEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * g) := by
  rw [sourceKPAdelicNonconstantEisenstein_upper, sourceKPAdelicNonconstantEisenstein_upper,
    sourceKPAdelicCompactEisenstein_upper_rational K hζ hs g y a]

end
end ArtinMatthews
