module

public import ArtinMatthews.SourceReflectionPositiveRetainedTwist
public import ArtinMatthews.SourceReflectionPositiveTwistBranch
public import ArtinMatthews.SourceReflectionPositiveTwistBranchSupport
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

/-! The active-branch partition on the actual positive seed keeps the
retained diagonal, every exterior upper translation and the common
seed argument in their original order. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators AdeleRing

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "U" => sourceReflectionPositiveTwistAdele K hζ S₀
local notation "wt" => sourceReflectionPositiveTwistWeight K hζ S₀
local notation "Seed" => sourceKPRetainedSeedFourierAt K hζ S

attribute [local instance] positiveTwistLabelFintype

def sourceReflectionPositiveRetainedBranch
    (e : E) (active : Finset PE) (R M : S → ℕ) (m : Kˣ)
    {T : ℝ} (hT : 1 ≤ T) (q₀ : Gf) (z : ∀ P : S, (P.val.adicCompletion K)ˣ) : ℂ :=
  ∑ u : SourceReflectionPositiveTwistLabels K S₀ e,
    if ∀ P : e.support, u P ≠ 0 ↔ P.val ∈ active then
      wt e u * Seed R M hT m q₀ (D (sourceKPRetainedDiagonalUnit K S z) * Nf (U e u))
    else 0

theorem sourceReflectionPositiveRetainedBranch_eq_finite
    (e : E) (active : Finset PE) (R M : S → ℕ) (m : Kˣ)
    {T : ℝ} (hT : 1 ≤ T) (q₀ : Gf) (z : ∀ P : S, (P.val.adicCompletion K)ˣ) :
    sourceReflectionPositiveRetainedBranch K hζ S₀ e active R M m hT q₀ z =
      sourceReflectionPositiveTwistBranch K hζ S₀ e active (Seed R M hT m q₀)
        (D (sourceKPRetainedDiagonalUnit K S z)) := by
  unfold sourceReflectionPositiveRetainedBranch sourceReflectionPositiveTwistBranch
  apply Finset.sum_congr rfl
  intro u _
  rw [(sourceReflectionPositiveTwistAdele_commute_retained K hζ S₀ e u z).eq]

theorem sourceReflectionPositiveRetainedBranch_eq
    (hS : standardWeilBadPlaces K ⊆ S) (e : E) (active : Finset PE) (R M : S → ℕ) (m : Kˣ)
    (x : sourceRing K S₀) (hx : (m:K) = (x:K))
    {T : ℝ} (hT : 1 ≤ T) (q₀ : Gf) (z : ∀ P : S, (P.val.adicCompletion K)ˣ) :
    sourceReflectionPositiveRetainedBranch K hζ S₀ e active R M m hT q₀ z =
      sourceReflectionPositiveTwistBranchFactor K hζ S₀ e active x *
        Seed R M hT m q₀ (D (sourceKPRetainedDiagonalUnit K S z)) := by
  rw [sourceReflectionPositiveRetainedBranch_eq_finite, sourceReflectionPositiveTwistBranch_eq K hζ S₀ hS e active m x hx]
  exact sourceReflectionRetainedSeedFourierAt_left_finite_upper K hζ S₀ R M m hT q₀ _

theorem sourceReflectionPositiveRetainedBranch_sum_powerset
    (e : E) (R M : S → ℕ) (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (q₀ : Gf)
    (z : ∀ P : S, (P.val.adicCompletion K)ˣ) :
    (∑ active ∈ e.support.powerset, sourceReflectionPositiveRetainedBranch K hζ S₀ e active R M m hT q₀ z) =
      sourceReflectionPositiveRetainedTwist K hζ S₀ e R M m hT q₀ z := by
  simp_rw [sourceReflectionPositiveRetainedBranch_eq_finite]
  rw [sourceReflectionPositiveTwistBranch_sum_powerset]
  unfold sourceReflectionPositiveFiniteTwist sourceReflectionPositiveRetainedTwist
  apply Finset.sum_congr rfl
  intro u _
  rw [(sourceReflectionPositiveTwistAdele_commute_retained K hζ S₀ e u z).eq]

end
end ArtinMatthews
