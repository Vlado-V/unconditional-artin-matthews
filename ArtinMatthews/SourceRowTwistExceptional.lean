module

public import ArtinMatthews.SourceRowTwistFamily
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

/-! The exceptional rows in the literal source are exactly the selected
primitive twists with a zero in the stated box. Old modulus deletion does
not create zeros in this region. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)
variable {ι : Type} [Fintype ι] (f : ι → {u : sourceRing F S₀ // u ≠ 0})
local notation "I" => SourceNonprincipalTwistRow F hζ S₀ η hM f
local notation "D" => sourceRowTwistFamilyModulus F hζ S₀ η hM f
local notation "χ" => sourceRowTwistFamilyCharacter F hζ S₀ η hM f
local notation "T" => sourceRowTwistConductorSupport F hζ S₀ η hM f
local notation "A" => sourceRowTwistCharactersAt F hζ S₀ η hM f

/-- Use the actual finite primitive zero detector at the chosen conductor. -/
def sourceRowTwistExceptionalRows (U r : ℝ) : Finset I :=
  Finset.univ.filter (fun i => primitiveZeroCoefficient F (D i) (A (D i)) U r ((χ) i).coefficient)

local notation "E" => sourceRowTwistExceptionalRows F hζ S₀ η hM f

theorem sourceRowTwistExceptionalRows_count (U r : ℝ)
    (hf : ∀ i j, (∃ a : F, a ^ 6 = ((f i).val : F) / ((f j).val : F)) → i = j) :
    (∑ N ∈ T, ((primitiveExceptionalCoefficients F N (A N) U r).card : ℝ)) =
      ((E U r).card : ℝ) := by
  have h := sourceRowTwistFamily_dependent_count_sum F hζ S₀ η hM f hf
    (fun N a => primitiveZeroCoefficient F N (A N) U r a)
  exact_mod_cast h

theorem sourceRowTwistExceptionalRows_complement_coeff (U r : ℝ) (i : I)
    (hi : i ∉ E U r) :
    ((χ) i).coefficient ∉ primitiveExceptionalCoefficients F (D i) (A (D i)) U r := by
  intro h
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩)

theorem sourceRowTwistExceptionalRows_mem_iff (U r : ℝ)
    (hf : ∀ i j, (∃ a : F, a ^ 6 = ((f i).val : F) / ((f j).val : F)) → i = j) (i : I) :
    i ∈ E U r ↔ ∃ z : ℂ, (249/250 : ℝ) ≤ z.re ∧ |z.im| ≤ 4*U^r ∧
      ((χ) i).primitiveContinued (D i).property
        (sourceRowTwistFamilyCharacter_primitive F hζ S₀ η hM f i) z = 0 := by
  constructor
  · intro h
    obtain ⟨ψ, hψ, he, hp, z, hz, him, hz0⟩ := (Finset.mem_filter.mp h).2
    obtain ⟨j, hj, htrans⟩ := (mem_finiteIdealCharactersAt D χ (D i) ψ).mp hψ
    have hj' : ((χ) j).coefficient = ((χ) i).coefficient :=
      (transportIdealRayCharacter_coefficient hj (χ j)).symm.trans
        ((congrArg (fun θ : EvenIdealRayCharacter F (D i).val => θ.coefficient) htrans).trans he)
    have hji := sourceRowTwistFamilyCharacter_coefficient_injective F hζ S₀ η hM f hf hj'
    subst j
    have hψ' : χ i = ψ := htrans
    subst ψ
    exact ⟨z, hz, him, hz0⟩
  · rintro ⟨z, hz, him, hz0⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, χ i,
      sourceRowTwistFamilyCharacter_mem F hζ S₀ η hM f i, rfl,
      sourceRowTwistFamilyCharacter_primitive F hζ S₀ η hM f i, z, hz, him, hz0⟩

theorem sourceRowTwistExceptionalRows_complement_nonvanishing (U r : ℝ) (i : I)
    (hi : i ∉ E U r) (z : ℂ) (hz : (249/250 : ℝ) ≤ z.re) (him : |z.im| ≤ 4*U^r) :
    ((χ) i).primitiveContinued (D i).property
      (sourceRowTwistFamilyCharacter_primitive F hζ S₀ η hM f i) z ≠ 0 :=
  primitiveExceptionalCoefficients_complement_nonvanishing F (D i) (A (D i)) U r (χ i)
    (sourceRowTwistFamilyCharacter_mem F hζ S₀ η hM f i)
    (sourceRowTwistFamilyCharacter_primitive F hζ S₀ η hM f i)
    (sourceRowTwistExceptionalRows_complement_coeff F hζ S₀ η hM f U r i hi) z hz him

theorem sourceRowTwistExceptionalRows_complement_reciprocalDomain (U r : ℝ) (i : I)
    (hi : i ∉ E U r) (z : ℂ) (hz : (249/250 : ℝ) ≤ z.re) (him : |z.im| ≤ 4*U^r) :
    z ∈ sourceRayReciprocalDomain F (sourceRowKummerTwist F hζ S₀
      (f i.val).val (f i.val).property η hM)
      (sourceRowTwistFamilyOldModulus_ne_bot F S₀ hM f i.val) := by
  unfold sourceRayReciprocalDomain
  rw [ite_eq_left i.property]
  intro hzero
  have h := (sourceRowTwistNonprincipal_zero_iff F hζ S₀
    (f i.val).val (f i.val).property η hM z (by linarith)).mp hzero
  exact sourceRowTwistExceptionalRows_complement_nonvanishing F hζ S₀ η hM f U r i hi z hz him h

end
end ArtinMatthews.SourceEulerAssembly
