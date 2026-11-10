module

public import ArtinMatthews.KummerTwistedPrimitiveFamily
public import ArtinMatthews.VaryingKummerAnalyticHeckeFiniteEulerContinuation
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

/-! Actual exceptional twisted rows and the old-modulus reciprocal bound.
The exceptional condition is an actual zero of the chosen primitive
continuation, and finite regrouping preserves its exact row count. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
variable [NumberField.IsTotallyComplex K]

def twistedPrimitiveExceptionalRows {M : Ideal (𝓞 K)} {η : EvenIdealRayCharacter K M}
    {hM : M ≠ ⊥} {ζ : K} {hζ : IsPrimitiveRoot ζ 6}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {N : ℕ}
    (d : ∀ i, BoundedKummerTwistedPrimitiveDatum η hM hζ S N i) (U r : ℝ) :
    Finset (KummerTwistedNonprincipalIndex d) :=
  Finset.univ.filter (fun i => primitiveZeroCoefficient K (twistedFamilyModulus d i)
    (twistedPrimitiveCharactersAt d (twistedFamilyModulus d i)) U r
    (twistedFamilyCharacter d i).coefficient)

theorem exists_twistedKummer_good_family (K : Type) [Field K] [NumberField K]
    [Algebra K ℂ] [NumberField.IsTotallyComplex K] :
    ∃ r C U₀ : ℝ, 0 < r ∧ r < 1/10 ∧ 0 < C ∧ 2 ≤ U₀ ∧
      (∀ {M : Ideal (𝓞 K)} (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
        {ζ : K} (hζ : IsPrimitiveRoot ζ 6) (S : Finset (HeightOneSpectrum (𝓞 K)))
        (_hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ)
        (d : ∀ i, BoundedKummerTwistedPrimitiveDatum η hM hζ S N i)
        (U : ℝ), U₀ ≤ U → twistedPrimitiveConductorBudget M S N ≤ U →
        ((twistedPrimitiveExceptionalRows d U r).card : ℝ) ≤ C*U^(1/2 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧
        ∀ {M : Ideal (𝓞 K)} (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
        {ζ : K} (hζ : IsPrimitiveRoot ζ 6) (S : Finset (HeightOneSpectrum (𝓞 K)))
        (_hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ)
        (d : ∀ i, BoundedKummerTwistedPrimitiveDatum η hM hζ S N i)
        (U : ℝ), U₀ ≤ U → twistedPrimitiveConductorBudget M S N ≤ U →
        ∀ i : KummerTwistedNonprincipalIndex d,
        i ∉ twistedPrimitiveExceptionalRows d U r →
        ∀ s : ℂ, (499/500 : ℝ) ≤ s.re → |s.im| ≤ 2*U^r →
          ‖((d i.1).character.idealCoprimeContinued (d i.1).modulus.property (d i.1).primitive
            (twistedKummerOldModulus M S N i.1) s)⁻¹‖ ≤ B*U^ε) := by
  obtain ⟨r,C,U₀,hr,hr',hC,hU₀,hcount,hgood⟩ :=
    exists_actual_primitive_good_family_with_deletions K
  refine ⟨r,C,U₀,hr,hr',hC,hU₀,?_,?_⟩
  · intro M η hM ζ hζ S hClass N d U hU hbudget
    have H := hcount U hU (twistedPrimitiveFamilySupport d) (twistedPrimitiveCharactersAt d)
      (fun f hf => (twistedPrimitiveFamilySupport_norm_le d f hf).trans hbudget)
      (fun f _ ψ hψ => twistedPrimitiveCharactersAt_primitive d f ψ hψ)
      (fun f _ ψ hψ => twistedPrimitiveCharactersAt_nonprincipal d f ψ hψ)
    have he := twistedPrimitiveFamily_dependent_count_sum d hClass
      (fun f a => primitiveZeroCoefficient K f (twistedPrimitiveCharactersAt d f) U r a)
    have hcast : ((twistedPrimitiveExceptionalRows d U r).card : ℝ) =
        ∑ f ∈ twistedPrimitiveFamilySupport d,
          ((primitiveExceptionalCoefficients K f (twistedPrimitiveCharactersAt d f) U r).card : ℝ) := by
      exact_mod_cast he.symm
    exact hcast.trans_le H
  · intro ε hε
    obtain ⟨B,hB,hrec⟩ := hgood ε hε
    refine ⟨B,hB,?_⟩
    intro M η hM ζ hζ S hClass N d U hU hbudget i hi s hs him
    have hcomp : (twistedFamilyCharacter d i).coefficient ∉
        primitiveExceptionalCoefficients K (twistedFamilyModulus d i)
          (twistedPrimitiveCharactersAt d (twistedFamilyModulus d i)) U r := by
      intro h
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩)
    exact hrec U hU (twistedPrimitiveFamilySupport d) (twistedPrimitiveCharactersAt d)
      (fun f hf => (twistedPrimitiveFamilySupport_norm_le d f hf).trans hbudget)
      (fun f _ ψ hψ => twistedPrimitiveCharactersAt_primitive d f ψ hψ)
      (fun f _ ψ hψ => twistedPrimitiveCharactersAt_nonprincipal d f ψ hψ)
      (twistedFamilyModulus d i) (twistedFamilyModulus_mem d i)
      (twistedFamilyCharacter d i) (twistedFamilyCharacter_mem d i) (d i.1).primitive hcomp
      (twistedKummerOldModulus M S N i.1) (twistedKummerOldModulus_ne_zero hM S N i.1)
      ((twistedKummerOldModulus_norm_le M S hClass N i.1).trans hbudget) s hs him

end
end ArtinMatthews
