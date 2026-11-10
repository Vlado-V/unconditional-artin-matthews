module

public import ArtinMatthews.SourceAdelicTraceHaar
public import ArtinMatthews.SourceKPAdelicCoordinateIntertwiner
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

/-! The measured outgoing value is left upper invariant and right
fixed by the exact original deep compact level. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "A" => 𝔸[K]
local notation "G" => SourceKPAdelicProjective K hζ
local notation "T" => sourceKPAdelicCoveringTorus K hζ
local notation "D" => sourceKPAdelicDeepCompact K hζ
local notation "F" => sourceKPAdelicCompactSection K hζ
local notation "W" => sourceKPAdelicProjectiveWeyl K hζ
local notation "N" => sourceKPAdelicUpperLift K hζ
local notation "M" => sourceKPAdelicSphericalIntertwinerValue K hζ (sourceKPAdelicTraceProduct K)
local notation "C" => sourceKPAdelicCoordinateKernel K hζ

local instance sourceKPAdelicOutgoingTranslationMeasurable : MeasurableSpace A := borel A
local instance sourceKPAdelicOutgoingTranslationBorel : BorelSpace A := ⟨rfl⟩

theorem sourceKPAdelicOutgoingKernel_upper (s : ℂ) (u : A) (g : G) (t : T) (x : A) :
    C s (N u*g) t x = C s g t (x+u) := by
  have h : W*N x*(N u*g) = W*N (x+u)*g := by
    rw [sourceKPAdelicUpperLift_add K hζ x u]
    group
  unfold sourceKPAdelicCoordinateKernel
  rw [h]

theorem sourceKPAdelicOutgoingValue_upper (s : ℂ) (u : A) (g : G) :
    M s (N u*g) = M s g := by
  apply Subtype.ext
  funext t
  simp only [sourceKPAdelicSphericalIntertwinerValue_apply]
  simp_rw [sourceKPAdelicOutgoingKernel_upper K hζ s u g]
  rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
  exact integral_add_right_eq_self _ u

theorem sourceKPAdelicOutgoingKernel_deep_right (s : ℂ) (g : G) (k : D) (t : T) (x : A) :
    C s (g*k.val) t x = C s g t x := by
  have h := congrArg (fun f : SourceKPAdelicPrincipalSeries K hζ s =>
    (f.val (W*N x*g)).val t) (sourceKPAdelicCompactSection_right K hζ s k)
  change ((F s).val ((W*N x*g)*k.val)).val t = ((F s).val (W*N x*g)).val t at h
  unfold sourceKPAdelicCoordinateKernel
  rw [← mul_assoc]
  exact h

theorem sourceKPAdelicOutgoingValue_deep_right (s : ℂ) (g : G) (k : D) :
    M s (g*k.val) = M s g := by
  apply Subtype.ext
  funext t
  simp only [sourceKPAdelicSphericalIntertwinerValue_apply]
  simp_rw [sourceKPAdelicOutgoingKernel_deep_right K hζ s g k]

end
end ArtinMatthews
