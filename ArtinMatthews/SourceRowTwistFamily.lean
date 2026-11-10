module

public import ArtinMatthews.FiniteIdealCharacterFamily
public import ArtinMatthews.SourceRowContinuedEuler
public import ArtinMatthews.IdealRayPrimitivePresentation
public import ArtinMatthews.SourceRowExteriorRay
public import ArtinMatthews.SourceRowTwistSeparation
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

/-! Regroup the literal source nonprincipal twists at their actual primitive
conductors. Distinct sixth-power classes give distinct coefficient functions;
the primitive descent never changes the old Euler deletion. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)
variable {ι : Type} (f : ι → {u : sourceRing F S₀ // u ≠ 0})
local notation "S" => sourceHilbertSet F S₀

abbrev SourceNonprincipalTwistRow :=
  {i : ι // (sourceRowKummerTwist F hζ S₀ (f i).val (f i).property η hM).IsNonprincipal}

local notation "I" => SourceNonprincipalTwistRow F hζ S₀ η hM f
local notation "d" => fun i : I => sourceRowTwistPrimitive F hζ S₀
  (Subtype.val (f (Subtype.val i))) (Subtype.property (f (Subtype.val i))) η hM

omit [IsTotallyComplex F] in
/-- The original row conductor, including the fixed twist modulus. -/
def sourceRowTwistFamilyOldModulus (i : ι) : Ideal (𝓞 F) :=
  M * sixthKummerSharpIdeal S (sourceRowFieldUnit F S₀ (f i).val (f i).property)

omit [IsTotallyComplex F] in
include hM in
theorem sourceRowTwistFamilyOldModulus_ne_bot (i : ι) :
    sourceRowTwistFamilyOldModulus F S₀ (M := M) f i ≠ ⊥ :=
  mul_ne_zero hM (sixthKummerSharpIdeal_ne_zero S
    (sourceRowFieldUnit F S₀ (f i).val (f i).property))

omit [IsTotallyComplex F] in
include hζ in
theorem sourceRowTwistFamilyOldModulus_norm_le (i : ι) :
    (sourceRowTwistFamilyOldModulus F S₀ (M := M) f i).absNorm ≤
      M.absNorm * (sixthKummerFixedIdeal S).absNorm *
        sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ (f i).val (f i).property) :=
  sourceRowKummerTwist_modulus_norm F S₀ hζ (f i).val (f i).property (M := M)

def sourceRowTwistFamilyModulus (i : I) : IdealConductorModulus F := (d i).modulus

def sourceRowTwistFamilyCharacter (i : I) :
    EvenIdealRayCharacter F (sourceRowTwistFamilyModulus F hζ S₀ η hM f i).val := (d i).character

local notation "D" => sourceRowTwistFamilyModulus F hζ S₀ η hM f
local notation "χ" => sourceRowTwistFamilyCharacter F hζ S₀ η hM f

theorem sourceRowTwistFamilyCharacter_primitive (i : I) :
    IsPrimitiveOnIdeals ((χ) i).residue := (d i).primitive

theorem sourceRowTwistFamilyCharacter_nonprincipal (i : I) : ((χ) i).IsNonprincipal :=
  (sourceRowKummerTwist F hζ S₀ (f i.val).val (f i.val).property η hM).primitiveIdeal_isNonprincipal
    (sourceRowTwistFamilyOldModulus_ne_bot F S₀ hM f i.val)
    (D i).val (d i).old_le (χ i) (d i).agrees i.property

theorem sourceRowTwistFamilyCharacter_coefficient_injective
    (hf : ∀ i j, (∃ a : F, a ^ 6 = ((f i).val : F) / ((f j).val : F)) → i = j) :
    Function.Injective (fun i => ((χ) i).coefficient) := by
  intro i j hij
  exact Subtype.ext (sourceRowTwistPrimitive_coeff_injective F hζ S₀ η hM f hf hij)

variable [Fintype ι]

def sourceRowTwistConductorSupport : Finset (IdealConductorModulus F) :=
  finiteIdealConductorSupport D

def sourceRowTwistCharactersAt (N : IdealConductorModulus F) :
    Finset (EvenIdealRayCharacter F N.val) := finiteIdealCharactersAt D χ N

local notation "T" => sourceRowTwistConductorSupport F hζ S₀ η hM f
local notation "A" => sourceRowTwistCharactersAt F hζ S₀ η hM f

theorem sourceRowTwistConductorSupport_norm_le (U : ℝ)
    (hU : ∀ i, ((sourceRowTwistFamilyOldModulus F S₀ (M := M) f i).absNorm : ℝ) ≤ U)
    (N : IdealConductorModulus F) (hN : N ∈ T) : (N.val.absNorm : ℝ) ≤ U := by
  apply finiteIdealConductorSupport_norm_le D U _ N hN
  intro i
  exact (Nat.cast_le.mpr (d i).norm_le).trans (hU i.val)

theorem sourceRowTwistCharactersAt_primitive (N : IdealConductorModulus F)
    (ψ : EvenIdealRayCharacter F N.val) (hψ : ψ ∈ A N) : IsPrimitiveOnIdeals ψ.residue :=
  finiteIdealCharactersAt_primitive D χ (sourceRowTwistFamilyCharacter_primitive F hζ S₀ η hM f) N ψ hψ

theorem sourceRowTwistCharactersAt_nonprincipal (N : IdealConductorModulus F)
    (ψ : EvenIdealRayCharacter F N.val) (hψ : ψ ∈ A N) : ψ.IsNonprincipal :=
  finiteIdealCharactersAt_nonprincipal D χ
    (sourceRowTwistFamilyCharacter_nonprincipal F hζ S₀ η hM f) N ψ hψ

theorem sourceRowTwistFamilyModulus_mem (i : I) : D i ∈ T :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem sourceRowTwistFamilyCharacter_mem (i : I) : χ i ∈ A (D i) :=
  (mem_finiteIdealCharactersAt D χ _ _).mpr ⟨i, rfl, rfl⟩

theorem sourceRowTwistFamily_dependent_count_sum
    (hf : ∀ i j, (∃ a : F, a ^ 6 = ((f i).val : F) / ((f j).val : F)) → i = j)
    (P : IdealConductorModulus F → (integralFractionalIdeals F → ℂ) → Prop) :
    (∑ N ∈ T, (((A N).image (fun ψ => ψ.coefficient)).filter (P N)).card) =
      (Finset.univ.filter (fun i => P (D i) ((χ) i).coefficient)).card :=
  finiteIdealCharactersAt_dependent_filter_card_sum D χ
    (sourceRowTwistFamilyCharacter_coefficient_injective F hζ S₀ η hM f hf) P

end
end ArtinMatthews.SourceEulerAssembly
