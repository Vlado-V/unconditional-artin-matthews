module

public import ArtinMatthews.PrincipalDedekindAbsoluteContour
public import ArtinMatthews.SourceContinuedPoissonRowIntegral
public import ArtinMatthews.SourceNonprincipalFrequencyDyads
public import ArtinMatthews.SourceProbeComparison
public import ArtinMatthews.SourceRowTwistDyadicExcluded
public import ArtinMatthews.SourceContinuedPoissonGoodDyadicBound
public import ArtinMatthews.SourceContinuedPoissonMagnitude
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

/-! Instantiate the genuine exceptional detector and good rectangle on
each finite dyad of actual source orbit representatives. The coefficient
injectivity premise is discharged by their proved sixth-class separation. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators
open VaryingKummerAnalytic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "I" => sourceContinuedPoissonRowIntegral F S₀ hζ η hJ
local notation "D" => SourceNonprincipalFrequencyDyad F S₀

omit [IsTotallyComplex F] in
def sourceNonprincipalDyadRepresentative (j : ℕ) (i : D j) : {u : R // u ≠ 0} :=
  sourceFrequencyRepresentative F hζ S₀ i.val.val

local notation "f" => sourceNonprincipalDyadRepresentative F S₀ hζ

omit [IsTotallyComplex F] in
theorem sourceNonprincipalDyadRepresentative_exterior_norm_le (j : ℕ) (i : D j) :
    (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ ((f j i).val) ((f j i).property)) : ℝ) ≤
      2*(2 : ℝ)^j := by
  have h := (sourceNonprincipalFrequencyDyad_frequency_bounds F S₀ hζ i).2.le
  change sourcePoissonFrequencyNorm F S₀ (f j i) ≤ _ at h
  rw [sourcePoissonFrequencyNorm_eq_exterior F S₀ hζ] at h
  exact h

def sourceNonprincipalDyadExcluded (j : ℕ) (r : ℝ) : Finset (D j) :=
  sourceRowTwistDyadicExcludedRows F S₀ hζ η hJ (f j) ((2 : ℝ)^j) r

local notation "E" => sourceNonprincipalDyadExcluded F S₀ hζ η hJ

theorem exists_sourceNonprincipalDyad_good_bounds
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) :
    ∃ r C U₀ : ℝ, 0 < r ∧ r < 1/10 ∧ 0 < C ∧ 2 ≤ U₀ ∧
      (∀ j : ℕ, U₀ ≤ (2 : ℝ)^j → ((E j r).card : ℝ) ≤ C*((2 : ℝ)^j)^(1/2 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∃ B : ℝ, 0 < B ∧
        ∀ j : ℕ, U₀ ≤ (2 : ℝ)^j → ∀ i : D j, i ∉ E j r → ∀ Z : ℝ, 1 ≤ Z →
          ‖I v (f j i) (Z^(9/10 : ℝ)) (Z^(133/1000 : ℝ)) Z 4 4 2‖ ≤
            B*(Z^(sourceContourExponent (499/500) (3/1000) (2/5))*((2 : ℝ)^j)^(1/10+ε)+
              Z^(sourceContourExponent principalProbeSigma (3/1000) (2/5))*((2 : ℝ)^j)^(1/10+ε-r*(n : ℝ)))) := by
  obtain ⟨r, C, U₀, hr, hr', hC, hU₀, hcount, hgood⟩ := exists_sourceRowTwist_dyadic_good_family F S₀ hζ η hJ
  refine ⟨r, 1+C, U₀, hr, hr', by positivity, hU₀, ?_, ?_⟩
  · intro j hU
    have hq := sourceNonprincipalDyadRepresentative_exterior_norm_le F S₀ hζ j
    have hs (i k : D j) (h : ∃ a : F, a^6 = ((f j i).val : F)/((f j k).val : F)) : i = k :=
      sourceNonprincipalFrequencyDyad_distinct_sixth F S₀ hζ i k h
    have h := hcount (f j) ((2 : ℝ)^j) hU hq hs
    exact sourceRowTwistDyadicExcludedRows_real_card_bound F S₀ hζ η hJ (f j) _ r C (by linarith) hs h
  · intro ε hε n
    obtain ⟨B, hB, hb⟩ := hgood (ε/2) (by positivity)
    obtain ⟨C', hC', h⟩ := exists_sourceContinuedPoissonRow_good_dyadic_bound_of_reciprocal F S₀ hζ η hJ hcut v
      ε hε n B hB
    refine ⟨C', hC', ?_⟩
    intro j hU i hi Z hZ
    have hq := sourceNonprincipalDyadRepresentative_exterior_norm_le F S₀ hζ j
    have hN := sourceNonprincipalFrequencyDyad_frequency_bounds F S₀ hζ i
    have hu := sourceNonprincipalFrequency_not_sixth F S₀ hζ i.val
    obtain ⟨hnp, hn⟩ := (sourceRowTwistDyadicExcludedRows_not_mem_iff F S₀ hζ η hJ (f j) _ r i).mp hi
    apply h (f j) i hu _ r (by linarith) hr.le hi hN.1 hN.2.le _ Z hZ
    intro ξ hξ him
    have hp : 0 ≤ ((2 : ℝ)^j)^r := by positivity
    exact hb (f j) ((2 : ℝ)^j) hU hq ⟨i,hnp⟩ hn ξ hξ (him.trans (by linarith))

end
end ArtinMatthews.SourceEulerAssembly
