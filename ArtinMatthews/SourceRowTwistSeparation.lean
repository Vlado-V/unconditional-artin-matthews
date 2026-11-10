module

public import ArtinMatthews.SourceRowContinuedEuler
public import ArtinMatthews.ArtinFrobeniusTwistedSeparation
public import ArtinMatthews.SourceRowTwistCommonFrobenius
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Actual source primitive twists separate sixth-power classes. The
comparison takes place in the common field of the two literal radicals
and uses primes outside both old moduli and the common modulus. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators AngularLambda VaryingKummerAnalytic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)
local notation "R" => sourceRing F S₀
local notation "S" => sourceHilbertSet F S₀

theorem sourceRowTwistPrimitive_coeff_eq_implies_sixth (u v : R) (hu : u ≠ 0) (hv : v ≠ 0)
    (he : (sourceRowTwistPrimitive F hζ S₀ u hu η hM).character.coefficient =
      (sourceRowTwistPrimitive F hζ S₀ v hv η hM).character.coefficient) :
    ∃ a : F, a ^ 6 = (u : F) / (v : F) := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let u₀ := sourceRowFieldUnit F S₀ u hu
  let v₀ := sourceRowFieldUnit F S₀ v hv
  let A : Finset F := {(u₀ : F), (v₀ : F)}
  let := sixthKummerRowField_isAbelianGalois (sourcePrimitiveSix F hζ) A
  have huA : (u₀ : F) ∈ A := by simp [A]
  have hvA : (v₀ : F) ∈ A := by simp [A]
  let M₁ := M * sixthKummerSharpIdeal S u₀
  let M₂ := M * sixthKummerSharpIdeal S v₀
  let C := sourceRowCommonModulus F hζ A
  let d := sourceRowTwistPrimitive F hζ S₀ u hu η hM
  let e := sourceRowTwistPrimitive F hζ S₀ v hv η hM
  let χ := sixthKummerRowCharacter (sourcePrimitiveSix F hζ) A (u₀ : F) huA u₀.ne_zero
  let θ := sixthKummerRowCharacter (sourcePrimitiveSix F hζ) A (v₀ : F) hvA v₀.ne_zero
  have hEq : χ = θ :=
    ArtinRay.galoisCharacter_eq_of_twisted_coefficients M₁ M₂ C
      (mul_ne_zero hM (sixthKummerSharpIdeal_ne_zero S u₀))
      (mul_ne_zero hM (sixthKummerSharpIdeal_ne_zero S v₀))
      (sourceRowCommonModulus_ne_bot F hζ A) d.character e.character d.old_le e.old_le
      η.idealHom χ θ
      (sourceRowTwistPrimitive_common_prime F hζ S₀ u hu η hM A huA)
      (sourceRowTwistPrimitive_common_prime F hζ S₀ v hv η hM A hvA) he
  exact (sixthKummerRowCharacter_eq_iff_exists_sixthPower (sourcePrimitiveSix F hζ)
    A (u₀ : F) (v₀ : F) huA hvA u₀.ne_zero v₀.ne_zero).mp hEq

theorem sourceRowPrincipalTwists_imply_sixth (u v : R) (hu : u ≠ 0) (hv : v ≠ 0)
    (huP : ¬ (sourceRowKummerTwist F hζ S₀ u hu η hM).IsNonprincipal)
    (hvP : ¬ (sourceRowKummerTwist F hζ S₀ v hv η hM).IsNonprincipal) :
    ∃ a : F, a ^ 6 = (u : F) / (v : F) := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let u₀ := sourceRowFieldUnit F S₀ u hu
  let v₀ := sourceRowFieldUnit F S₀ v hv
  let A : Finset F := {(u₀ : F), (v₀ : F)}
  let := sixthKummerRowField_isAbelianGalois (sourcePrimitiveSix F hζ) A
  have huA : (u₀ : F) ∈ A := by simp [A]
  have hvA : (v₀ : F) ∈ A := by simp [A]
  let M₁ := M * sixthKummerSharpIdeal S u₀
  let M₂ := M * sixthKummerSharpIdeal S v₀
  let C := sourceRowCommonModulus F hζ A
  let χ := sixthKummerRowCharacter (sourcePrimitiveSix F hζ) A (u₀ : F) huA u₀.ne_zero
  let θ := sixthKummerRowCharacter (sourcePrimitiveSix F hζ) A (v₀ : F) hvA v₀.ne_zero
  have hEq : χ = θ := by
    apply ArtinRay.galoisCharacter_eq_of_twisted_good_prime_values M₁ M₂ C
      (mul_ne_zero hM (sixthKummerSharpIdeal_ne_zero S u₀))
      (mul_ne_zero hM (sixthKummerSharpIdeal_ne_zero S v₀))
      (sourceRowCommonModulus_ne_bot F hζ A) η.idealHom χ θ
    intro P h₁ h₂ hC
    let J := integralIdealFractionalUnit P.asIdeal P.ne_bot
    have hu1 : (sourceRowKummerTwist F hζ S₀ u hu η hM).idealHom J = 1 := by
      by_contra h
      exact huP ⟨P.asIdeal, P.ne_bot, h₁, h⟩
    have hv1 : (sourceRowKummerTwist F hζ S₀ v hv η hM).idealHom J = 1 := by
      by_contra h
      exact hvP ⟨P.asIdeal, P.ne_bot, h₂, h⟩
    exact (sourceRowTwist_common_prime F hζ S₀ u hu η hM A huA P hC).symm.trans
      (hu1.trans (hv1.symm.trans (sourceRowTwist_common_prime F hζ S₀ v hv η hM A hvA P hC)))
  exact (sixthKummerRowCharacter_eq_iff_exists_sixthPower (sourcePrimitiveSix F hζ)
    A (u₀ : F) (v₀ : F) huA hvA u₀.ne_zero v₀.ne_zero).mp hEq

theorem sourceRowTwistPrimitive_coeff_injective {ι : Type} (f : ι → {u : R // u ≠ 0})
    (hf : ∀ i j, (∃ a : F, a ^ 6 = ((f i).val : F) / ((f j).val : F)) → i = j) :
    Function.Injective (fun i => (sourceRowTwistPrimitive F hζ S₀
      (f i).val (f i).property η hM).character.coefficient) := by
  intro i j he
  exact hf i j (sourceRowTwistPrimitive_coeff_eq_implies_sixth F hζ S₀ η hM
    (f i).val (f j).val (f i).property (f j).property he)

theorem sourceRowPrincipalTwists_card_le_one {ι : Type} [Fintype ι]
    (f : ι → {u : R // u ≠ 0})
    (hf : ∀ i j, (∃ a : F, a ^ 6 = ((f i).val : F) / ((f j).val : F)) → i = j) :
    (Finset.univ.filter (fun i => ¬ (sourceRowKummerTwist F hζ S₀
      (f i).val (f i).property η hM).IsNonprincipal)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact hf i j (sourceRowPrincipalTwists_imply_sixth F hζ S₀ η hM
    (f i).val (f j).val (f i).property (f j).property (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)

end
end ArtinMatthews.SourceEulerAssembly
