module

public import ArtinMatthews.KummerCyclotomicTowerComplex
public import ArtinMatthews.ArtinRaySmallModulus
public import ArtinMatthews.KummerRowField
public import ArtinMatthews.VaryingKummerAnalyticRayIdealConductorOne
public import ArtinMatthews.ArtinFrobeniusCharacterInjectivity
public import ArtinMatthews.KummerRowDegree
public import ArtinMatthews.VaryingKummerAnalyticRayPrimitiveNonprincipal
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
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! Genuine ray-character realizations of finite sixth-Kummer rows. The
coefficient kernel is exactly the sixth-power relation. The displayed common
modulus is the honest discriminant-degree modulus; no tame linear conductor
estimate is claimed or substituted for the missing local argument. -/
namespace ArtinMatthews
open NumberField VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {F : Type} [Field F] [NumberField F] [Algebra F ℂ]
variable [NumberField.IsTotallyComplex F]

instance sixthKummerRowModulus_neZero (A : Finset F) :
    NeZero (discriminantDegreeModulus F (sixthKummerRowField A)) :=
  ⟨(discriminantDegreeModulus_pos F (sixthKummerRowField A)).ne'⟩

def sixthKummerRowRayCharacter {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (A : Finset F) (a : F) (ha : a ∈ A) (ha0 : a ≠ 0) :
    EvenRayCharacter F (discriminantDegreeModulus F (sixthKummerRowField A)) := by
  letI := sixthKummerRowField_isAbelianGalois hζ A
  exact ArtinRay.discriminantDegreeRayCharacter (sixthKummerRowCharacter hζ A a ha ha0)

theorem sixthKummerRowRayCharacter_idealHom {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (A : Finset F) (a : F) (ha : a ∈ A) (ha0 : a ≠ 0) :
    (sixthKummerRowRayCharacter hζ A a ha ha0).idealHom =
      GaloisIdealCharacter.idealHom F (sixthKummerRowField A)
        (sixthKummerRowCharacter hζ A a ha ha0) := by
  unfold sixthKummerRowRayCharacter
  rfl

theorem sixthKummerRowRayCharacter_coefficient_eq_iff {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (A : Finset F) (a b : F) (ha : a ∈ A) (hb : b ∈ A) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (sixthKummerRowRayCharacter hζ A a ha ha0).coefficient =
      (sixthKummerRowRayCharacter hζ A b hb hb0).coefficient ↔ ∃ t : F, t^6 = a/b := by
  let := sixthKummerRowField_isAbelianGalois hζ A
  change (ArtinRay.discriminantDegreeRayCharacter (sixthKummerRowCharacter hζ A a ha ha0)).coefficient =
    (ArtinRay.discriminantDegreeRayCharacter (sixthKummerRowCharacter hζ A b hb hb0)).coefficient ↔ _
  constructor
  · intro h
    exact (sixthKummerRowCharacter_eq_iff_exists_sixthPower hζ A a b ha hb ha0 hb0).mp
      (ArtinRay.discriminantDegreeRayCharacter_coefficient_injective h)
  · intro h
    exact congrArg (fun χ => (ArtinRay.discriminantDegreeRayCharacter χ).coefficient)
      ((sixthKummerRowCharacter_eq_iff_exists_sixthPower hζ A a b ha hb ha0 hb0).mpr h)

theorem sixthKummerRowRayCharacter_isNonprincipal {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (A : Finset F) (a : F) (ha : a ∈ A) (ha0 : a ≠ 0)
    (hpower : ¬∃ t : F, t^6 = a) :
    (sixthKummerRowRayCharacter hζ A a ha ha0).IsNonprincipal := by
  let := sixthKummerRowField_isAbelianGalois hζ A
  have hχ : sixthKummerRowCharacter hζ A a ha ha0 ≠ 1 :=
    fun h => hpower ((sixthKummerRowCharacter_one_iff_exists_sixthPower hζ A a ha ha0).mp h)
  exact ArtinRay.discriminantDegreeRayCharacter_isNonprincipal _ hχ

theorem sixthKummerRow_exists_primitive_character {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (A : Finset F) (a : F) (ha : a ∈ A) (ha0 : a ≠ 0)
    (hpower : ¬∃ t : F, t^6 = a) :
    ∃ (f : Ideal (𝓞 F)) (_hf : f ≠ ⊥)
      (_hfM : rationalModulusIdeal (𝓞 F)
        (discriminantDegreeModulus F (sixthKummerRowField A)) ≤ f)
      (Ψ : EvenIdealRayCharacter F f),
      OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals Ψ.residue ∧ Ψ.IsNonprincipal ∧
      f.absNorm ≤ (rationalModulusIdeal (𝓞 F)
        (discriminantDegreeModulus F (sixthKummerRowField A))).absNorm ∧
      (∀ I : RayClass.primeToModulusIdeals (rationalIdealRayModulus F
          (discriminantDegreeModulus F (sixthKummerRowField A))),
        Ψ.idealHom (I:FractionalIdealGroup F) =
          GaloisIdealCharacter.idealHom F (sixthKummerRowField A)
            (sixthKummerRowCharacter hζ A a ha ha0) (I:FractionalIdealGroup F)) := by
  let := sixthKummerRowField_isAbelianGalois hζ A
  obtain ⟨f,hf,hfM,Ψ,hprim,hΨ,hnorm,_hmask,hagree⟩ :=
    (sixthKummerRowRayCharacter hζ A a ha ha0).exists_primitive_nonprincipal_idealCharacter
      (sixthKummerRowRayCharacter_isNonprincipal hζ A a ha ha0 hpower)
  refine ⟨f,hf,hfM,Ψ,hprim,hΨ,hnorm,?_⟩
  intro I
  exact (hagree I).trans (DFunLike.congr_fun
    (sixthKummerRowRayCharacter_idealHom hζ A a ha ha0) (I : FractionalIdealGroup F))

def twelfthSixthRoot (q : ℕ) [NeZero q] : twelfthCyclotomicField q :=
  ⟨primeCyclotomicRoot 6,by
    change primeCyclotomicRoot 6 ∈ primeCyclotomicField (12*q)
    apply root_of_unity_mem_primeCyclotomicField (Nat.mul_pos (by decide) (NeZero.pos q))
    rw [show 12*q = 6*(2*q) by omega,pow_mul,primeCyclotomicRoot_pow (by decide : 0 < 6),one_pow]⟩

theorem twelfthSixthRoot_isPrimitiveRoot (q : ℕ) [NeZero q] :
    IsPrimitiveRoot (twelfthSixthRoot q) 6 :=
  IsPrimitiveRoot.of_map_of_injective (f := (twelfthCyclotomicField q).val)
    (primeCyclotomicRoot_isPrimitiveRoot (by decide : 0 < 6)) Subtype.val_injective

theorem twelfth_sixthKummerRow_coefficient_eq_iff (q : ℕ) [NeZero q]
    (A : Finset (twelfthCyclotomicField q)) (a b : twelfthCyclotomicField q)
    (ha : a ∈ A) (hb : b ∈ A) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (sixthKummerRowRayCharacter (twelfthSixthRoot_isPrimitiveRoot q) A a ha ha0).coefficient =
      (sixthKummerRowRayCharacter (twelfthSixthRoot_isPrimitiveRoot q) A b hb hb0).coefficient ↔
        ∃ t : twelfthCyclotomicField q, t^6 = a/b :=
  sixthKummerRowRayCharacter_coefficient_eq_iff (twelfthSixthRoot_isPrimitiveRoot q) A a b ha hb ha0 hb0

theorem twelfth_sixthKummerRow_absolute_finrank_le (q : ℕ) [NeZero q]
    (A : Finset (twelfthCyclotomicField q)) (hA : ∀ a ∈ A, a ≠ 0) :
    Module.finrank ℚ (sixthKummerRowField A) ≤ Nat.totient (12*q) * 6^A.card := by
  calc
    _ = Module.finrank ℚ (twelfthCyclotomicField q) *
        Module.finrank (twelfthCyclotomicField q) (sixthKummerRowField A) :=
      (Module.finrank_mul_finrank ℚ (twelfthCyclotomicField q) (sixthKummerRowField A)).symm
    _ ≤ _ := by
      rw [finrank_twelfthCyclotomicField]
      exact Nat.mul_le_mul_left _ (sixthKummerRowField_finrank_le (twelfthSixthRoot_isPrimitiveRoot q) A hA)

end
end ArtinMatthews
