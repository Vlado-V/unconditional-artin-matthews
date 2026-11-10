module

public import ArtinMatthews.FiniteIdealCharacterFamily
public import ArtinMatthews.KummerTwistedPrimitiveData
public import ArtinMatthews.KummerTwistedPrimitiveInjectivity
public import ArtinMatthews.SixthKummerSharpRows
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

/-! The actual nonprincipal part of a fixed-character twisted Kummer
family, regrouped by its primitive ideal conductors. The principal part
has at most one row; all remaining coefficient functions are distinct. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
variable [NumberField.IsTotallyComplex K]

def twistedPrimitiveConductorBudget (M : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) : ℝ :=
  (M.absNorm : ℝ) * (sixthKummerFixedIdeal S).absNorm * N

omit [Algebra K ℂ] [NumberField.IsTotallyComplex K] in
theorem twistedPrimitiveConductorBudget_ge_one {M : Ideal (𝓞 K)} (hM : M ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ twistedPrimitiveConductorBudget M S N := by
  have h₁ : 1 ≤ M.absNorm := Nat.one_le_iff_ne_zero.mpr
    (fun h => hM (Ideal.absNorm_eq_zero_iff.mp h))
  have h₂ : 1 ≤ (sixthKummerFixedIdeal S).absNorm := sixthKummerFixedIdeal_absNorm_pos S
  unfold twistedPrimitiveConductorBudget
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (Nat.ne_of_gt h₁) (Nat.ne_of_gt h₂)) (Nat.ne_of_gt hN)) :
      1 ≤ M.absNorm * (sixthKummerFixedIdeal S).absNorm * N)

omit [Algebra K ℂ] [NumberField.IsTotallyComplex K] in
theorem twistedKummerOldModulus_norm_le (M : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hClass : exteriorPrincipalizingPrimes K ⊆ S)
    (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    ((twistedKummerOldModulus M S N i).absNorm : ℝ) ≤ twistedPrimitiveConductorBudget M S N := by
  have h : (twistedKummerOldModulus M S N i).absNorm ≤
      M.absNorm * (sixthKummerFixedIdeal S).absNorm * N := by
    rw [twistedKummerOldModulus,map_mul,sixthKummerSharpIdeal_absNorm,← mul_assoc]
    exact Nat.mul_le_mul_left _ (exteriorBoundedIdealRow_radical_norm_le S hClass N i)
  unfold twistedPrimitiveConductorBudget
  exact_mod_cast h

variable {M : Ideal (𝓞 K)} {η : EvenIdealRayCharacter K M} {hM : M ≠ ⊥}
variable {ζ : K} {hζ : IsPrimitiveRoot ζ 6}
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {N : ℕ}
variable (d : ∀ i, BoundedKummerTwistedPrimitiveDatum η hM hζ S N i)

abbrev KummerTwistedNonprincipalIndex :=
  {i : ExteriorIdealRowIndex S N // (d i).character.IsNonprincipal}

def twistedFamilyModulus (i : KummerTwistedNonprincipalIndex d) : IdealConductorModulus K :=
  (d i.1).modulus

def twistedFamilyCharacter (i : KummerTwistedNonprincipalIndex d) :
    EvenIdealRayCharacter K (twistedFamilyModulus d i).val := (d i.1).character

def twistedPrimitiveFamilySupport : Finset (IdealConductorModulus K) :=
  finiteIdealConductorSupport (twistedFamilyModulus d)

def twistedPrimitiveCharactersAt (f : IdealConductorModulus K) :
    Finset (EvenIdealRayCharacter K f.val) :=
  finiteIdealCharactersAt (twistedFamilyModulus d) (twistedFamilyCharacter d) f

theorem twistedFamilyCharacter_coefficient_injective (hClass : exteriorPrincipalizingPrimes K ⊆ S) :
    Function.Injective (fun i => (twistedFamilyCharacter d i).coefficient) := by
  intro i j h
  exact Subtype.ext (boundedKummerTwistedPrimitiveDatum_coefficient_injective
    η hM hζ S hClass N d h)

omit [NumberField.IsTotallyComplex K] in
theorem twistedPrimitiveFamilySupport_norm_le (f : IdealConductorModulus K)
    (hf : f ∈ twistedPrimitiveFamilySupport d) :
    (f.val.absNorm : ℝ) ≤ twistedPrimitiveConductorBudget M S N := by
  apply finiteIdealConductorSupport_norm_le (twistedFamilyModulus d) _ _ f hf
  intro i
  change ((d i.1).modulus.val.absNorm : ℝ) ≤ _
  unfold twistedPrimitiveConductorBudget
  exact_mod_cast (d i.1).norm_le

omit [NumberField.IsTotallyComplex K] in
theorem twistedPrimitiveCharactersAt_primitive (f : IdealConductorModulus K)
    (ψ : EvenIdealRayCharacter K f.val) (hψ : ψ ∈ twistedPrimitiveCharactersAt d f) :
    IsPrimitiveOnIdeals ψ.residue :=
  finiteIdealCharactersAt_primitive (twistedFamilyModulus d) (twistedFamilyCharacter d)
    (fun i : KummerTwistedNonprincipalIndex d => (d i.1).primitive) f ψ hψ

omit [NumberField.IsTotallyComplex K] in
theorem twistedPrimitiveCharactersAt_nonprincipal (f : IdealConductorModulus K)
    (ψ : EvenIdealRayCharacter K f.val) (hψ : ψ ∈ twistedPrimitiveCharactersAt d f) :
    ψ.IsNonprincipal :=
  finiteIdealCharactersAt_nonprincipal (twistedFamilyModulus d) (twistedFamilyCharacter d)
    (fun i : KummerTwistedNonprincipalIndex d => i.2) f ψ hψ

omit [NumberField.IsTotallyComplex K] in
theorem twistedFamilyCharacter_mem (i : KummerTwistedNonprincipalIndex d) :
    twistedFamilyCharacter d i ∈ twistedPrimitiveCharactersAt d (twistedFamilyModulus d i) :=
  (mem_finiteIdealCharactersAt _ _ _ _).mpr ⟨i,rfl,rfl⟩

omit [NumberField.IsTotallyComplex K] in
theorem twistedFamilyModulus_mem (i : KummerTwistedNonprincipalIndex d) :
    twistedFamilyModulus d i ∈ twistedPrimitiveFamilySupport d :=
  Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem twistedPrimitiveFamily_dependent_count_sum (hClass : exteriorPrincipalizingPrimes K ⊆ S)
    (P : IdealConductorModulus K → (integralFractionalIdeals K → ℂ) → Prop) :
    (∑ f ∈ twistedPrimitiveFamilySupport d,
      (((twistedPrimitiveCharactersAt d f).image (fun ψ => ψ.coefficient)).filter (P f)).card) =
      (Finset.univ.filter (fun i => P (twistedFamilyModulus d i)
        (twistedFamilyCharacter d i).coefficient)).card :=
  finiteIdealCharactersAt_dependent_filter_card_sum _ _
    (twistedFamilyCharacter_coefficient_injective d hClass) P

end
end ArtinMatthews
