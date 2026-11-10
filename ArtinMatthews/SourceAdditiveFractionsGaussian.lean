module

public import ArtinMatthews.SourceReducedFractionTraceLift
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleAdditiveSieve
public import ArtinMatthews.GaussianCoordinateModularSieve
public import ArtinMatthews.SourceReducedFractionCoordinates
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleFrequencyBalanced
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Transport the existing checked Gaussian sieve along actual integer
coordinates. The coefficient functions are literal source additive phases. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain AllowedGenerators StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F}

local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "O" => (⊤ : Ideal (𝓞 F))
local notation "J" => IdealModuleFrequencyIndex F O top_ne_bot
local notation "coords" => idealModuleIntegerCoordinates F O top_ne_bot
local notation "radius" => idealModuleSieveReciprocalRadius F O top_ne_bot

/-- The source additive energy over actual finite rows already cleared
into the ring of integers. The compact-box application derives these
coordinate support bounds uniformly in the scale. -/
theorem sourceReducedFraction_gaussianDual (hζ : IsPrimitiveRoot ζ 12)
    (htrace : traceBadPlaces F ⊆ S) (δ : 𝓞 F) (hδ : δ ≠ 0)
    (hδS : ∀ P : HeightOneSpectrum (𝓞 F), P ∉ S → P.valuation F (δ : F) = 1)
    (a : E → R) (ha : ∀ e, a e ≠ 0)
    (hgen : ∀ e, (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {a e})
    (A : Finset R) (n : ∀ m ∈ A, 𝓞 F) (hn : ∀ m hm, (n m hm : F) = (m : F) * (δ : F))
    {H V : ℝ} (hH : 0 < H) (hV : 0 < V)
    (hA : ∀ m (hm : m ∈ A), (∑ j : J, (coords ⟨n m hm, by simp⟩ j : ℝ) ^ 2) ≤ H ^ 2)
    (P : Finset (SourceReducedFractionLabel F S₀ a)) (hP : ∀ p ∈ P, (q p.1 : ℝ) ≤ V)
    (b : SourceReducedFractionLabel F S₀ a → ℂ) :
    (∑ m ∈ A, ‖∑ p ∈ P, b p * sourceReducedFractionPhase F S₀ a ha p m‖ ^ 2) ≤
      (coordinateOptimizedSieveConstant J * (H ^ Module.finrank ℚ F + (radius V) ^ Module.finrank ℚ F)) *
        ∑ p ∈ P, ‖b p‖ ^ 2 := by
  choose x hx hdual using exists_sourceReducedFraction_traceLift F S₀ hζ a ha hgen htrace δ hδ hδS
  let β (p : SourceReducedFractionLabel F S₀ a) := (x p : F) / ((a p.1 : F) * (δ : F))
  let θ (p : SourceReducedFractionLabel F S₀ a) := idealModuleTraceCoordinates F O top_ne_bot (β p)
  let nc (m : R) : J → ℤ := if hm : m ∈ A then coords ⟨n m hm, by simp⟩ else 0
  have hnc (m : R) (hm : m ∈ A) : nc m = coords ⟨n m hm, by simp⟩ := by
    dsimp only [nc]
    rw [dite_eq_left hm]
  have hinj : Set.InjOn nc (A : Set R) := by
    intro m hm m' hm' hh
    have hmA : m ∈ A := hm
    have hmA' : m' ∈ A := hm'
    rw [hnc m hmA, hnc m' hmA'] at hh
    have he := idealModuleIntegerCoordinates_injective F O top_ne_bot hh
    have heF := congrArg (fun z : O => (z.val : F)) he
    change (n m hmA : F) = (n m' hmA' : F) at heF
    rw [hn m hmA, hn m' hmA'] at heF
    exact Subtype.ext (mul_right_cancel₀ (Subtype.coe_injective.ne hδ) heF)
  have hsupport : ∀ k ∈ A.image nc, (∑ j, (k j : ℝ) ^ 2) ≤ H ^ 2 := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
    rw [hnc m hm]
    exact hA m hm
  have hQ : 1 ≤ radius V := idealModuleSieveReciprocalRadius_one_le F O top_ne_bot V
  have hsmall : 1 / radius V ≤ idealModuleCoordinateSeparationRadius F O top_ne_bot V := by
    have hr := idealModuleCoordinateSeparationRadius_pos F O top_ne_bot hV
    have h := one_div_le_one_div_of_le (one_div_pos.mpr hr)
      (le_max_right 1 (1 / idealModuleCoordinateSeparationRadius F O top_ne_bot V))
    simpa only [idealModuleSieveReciprocalRadius, one_div_one_div] using h
  have hsep : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → ∀ k : J → ℤ,
      1 / radius V ≤ ‖(fun j => θ p j - θ p' j + (k j : ℝ))‖ := by
    intro p hp p' hp' hne k
    exact hsmall.trans (sourceReducedFraction_traceCoordinates_separated F S₀ a ha hgen htrace δ hδ hδS
      p p' hne (x p) (x p') (hx p) (hx p') (hdual p) (hdual p') (hP p hp) (hP p' hp') k)
  have hs := coordinate_modular_dual_sieve (Q := radius V) (a := 1 / H ^ 2) hQ
    (by positivity) P θ hsep (A.image nc) hsupport b
  rw [Finset.sum_image hinj] at hs
  have he (p : SourceReducedFractionLabel F S₀ a) (m : R) (hm : m ∈ A) :
      coordinatePhase (θ p) (nc m) = sourceReducedFractionPhase F S₀ a ha p m := by
    rw [hnc m hm, show θ p = idealModuleTraceCoordinates F O top_ne_bot (β p) from rfl,
      idealModule_coordinatePhase_eq_trace]
    exact (sourceReducedFractionPhase_eq_trace F S₀ a ha δ hδ p m (x p) (n m hm)
      (hn m hm) (hx p) (hdual p)).symm
  have hsum : (∑ m ∈ A, ‖∑ p ∈ P, b p * coordinatePhase (θ p) (nc m)‖ ^ 2) =
      ∑ m ∈ A, ‖∑ p ∈ P, b p * sourceReducedFractionPhase F S₀ a ha p m‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro m hm
    simp only [he _ m hm]
  rw [← hsum]
  refine hs.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  simpa only [idealModuleFrequencyIndex_card] using
    (coordinateAdditiveSieveBound_optimized (β := J) hH (zero_le_one.trans hQ))

end
end ArtinMatthews.SourcePhysical
