module

public import ArtinMatthews.KummerTwistedRowWeights
public import ArtinMatthews.KummerTwistedPrimitiveInjectivity
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

/-! A source arithmetic estimate for the actual chosen twisted family.
The exceptional dyadic row sum has exponent 1/2, while the complete row
sum has exponent 1. The fixed character and S enter only the displayed
conductor cost. No common-probe integral estimate is a premise. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

theorem exists_chosen_twistedKummer_dyadic_weighted
    (K : Type) [Field K] [NumberField K] [Algebra K ℂ] [NumberField.IsTotallyComplex K] :
    ∃ r C U₀ : ℝ, 0 < r ∧ r < 1/10 ∧ 0 < C ∧ 2 ≤ U₀ ∧
      ∀ {M : Ideal (𝓞 K)} (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
        {ζ : K} (hζ : IsPrimitiveRoot ζ 6) (S : Finset (HeightOneSpectrum (𝓞 K)))
        (hWild : sixthWildPrimes K ⊆ S) (hClass : exteriorPrincipalizingPrimes K ⊆ S)
        (N : ℕ) (U σ : ℝ), 1 ≤ U → (N : ℝ) ≤ 2*U → 0 ≤ σ →
        U₀ ≤ twistedPrimitiveConductorBudget M S N →
        let d := chosenKummerTwistedPrimitiveDatum η hM hζ S hWild hClass N
        (∑ i ∈ (twistedExcludedRows d (twistedPrimitiveConductorBudget M S N) r).filter
            (fun i => U ≤ exteriorRowIdealNorm i),
          (exteriorRowIdealNorm i)^(-σ)) ≤
          (1+C*(2*(M.absNorm : ℝ)*(sixthKummerFixedIdeal S).absNorm)^(1/2 : ℝ))*U^(1/2-σ) := by
  obtain ⟨r,C,U₀,hr,hr',hC,hU₀,hcount,_hgood⟩ := exists_twistedKummer_good_family K
  refine ⟨r,C,U₀,hr,hr',hC,hU₀,?_⟩
  intro M η hM ζ hζ S hWild hClass N U σ hU hNU hσ hV
  let d := chosenKummerTwistedPrimitiveDatum η hM hζ S hWild hClass N
  let A : ℝ := (M.absNorm : ℝ)*(sixthKummerFixedIdeal S).absNorm
  let V : ℝ := twistedPrimitiveConductorBudget M S N
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hVnonneg : 0 ≤ V := by dsimp [V,twistedPrimitiveConductorBudget]; positivity
  have hVU : V ≤ (2*A)*U := by
    have h := mul_le_mul_of_nonneg_left hNU hA
    dsimp [V,twistedPrimitiveConductorBudget,A] at h ⊢
    nlinarith
  have hpow : V^(1/2 : ℝ) ≤ (2*A)^(1/2 : ℝ)*U^(1/2 : ℝ) := by
    exact (Real.rpow_le_rpow hVnonneg hVU (by norm_num)).trans_eq
      (Real.mul_rpow (by positivity : 0 ≤ 2*A) hUpos.le)
  have hhalf : 1 ≤ U^(1/2 : ℝ) := Real.one_le_rpow hU (by norm_num)
  have hbad := hcount η hM hζ S hClass N d V hV le_rfl
  have hcard : ((twistedExcludedRows d V r).card : ℝ) ≤
      (1+C*(2*A)^(1/2 : ℝ))*U^(1/2 : ℝ) := by
    have he := twistedExcludedRows_card_le d hClass V r
    nlinarith [mul_le_mul_of_nonneg_left hpow hC.le]
  let T := (twistedExcludedRows d V r).filter (fun i => U ≤ exteriorRowIdealNorm i)
  have hTcard : (T.card : ℝ) ≤ (1+C*(2*A)^(1/2 : ℝ))*U^(1/2 : ℝ) := by
    have hle : (T.card : ℝ) ≤ (twistedExcludedRows d V r).card := by
      exact_mod_cast Finset.card_filter_le (twistedExcludedRows d V r) _
    exact hle.trans hcard
  have H := exteriorRow_weight_sum_of_card_bound T U σ
    (1+C*(2*A)^(1/2 : ℝ)) (1/2) hUpos hσ
    (fun i hi => (Finset.mem_filter.mp hi).2) hTcard
  simpa only [T,V,A,mul_assoc] using H

theorem chosenKummerTwistedPrimitiveCoefficientFamily_card
    {K : Type} [Field K] [NumberField K] [Algebra K ℂ] [NumberField.IsTotallyComplex K]
    {M : Ideal (𝓞 K)} (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 6) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hWild : sixthWildPrimes K ⊆ S) (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) :
    (Finset.univ.image (fun i =>
      (chosenKummerTwistedPrimitiveDatum η hM hζ S hWild hClass N i).character.coefficient)).card =
      (exteriorBoundedIdealRows S N).card*(exteriorUnitSixthRepresentatives S).card := by
  rw [Finset.card_image_of_injective _
    (boundedKummerTwistedPrimitiveDatum_coefficient_injective η hM hζ S hClass N _),
    Finset.card_univ,exteriorIdealRowIndex_card]

theorem chosenKummerTwistedPrimitive_nonprincipal_count_deficit
    {K : Type} [Field K] [NumberField K] [Algebra K ℂ] [NumberField.IsTotallyComplex K]
    {M : Ideal (𝓞 K)} (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 6) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hWild : sixthWildPrimes K ⊆ S) (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) :
    (exteriorBoundedIdealRows S N).card*(exteriorUnitSixthRepresentatives S).card-1 ≤
      (Finset.univ.filter (fun i =>
        (chosenKummerTwistedPrimitiveDatum η hM hζ S hWild hClass N i).character.IsNonprincipal)).card := by
  let d := chosenKummerTwistedPrimitiveDatum η hM hζ S hWild hClass N
  have he := Finset.card_filter_add_card_filter_not (fun i => (d i).character.IsNonprincipal)
    (s := (Finset.univ : Finset (ExteriorIdealRowIndex S N)))
  have hp := boundedKummerTwistedPrimitiveDatum_principal_count η hM hζ S hClass N d
  rw [Finset.card_univ,exteriorIdealRowIndex_card] at he
  change _ ≤ (Finset.univ.filter (fun i => (d i).character.IsNonprincipal)).card
  omega

end
end ArtinMatthews
