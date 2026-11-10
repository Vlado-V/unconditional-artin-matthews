module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.FieldTheory.Galois.Abelian
public import ArtinMatthews.KummerRadicalCyclic
public import Mathlib.Basic.Complex.Basic
public import ArtinMatthews.KummerCharacterKernel
public import Mathlib.Analysis.Complex.Polynomial.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine common sixth-radical field for a finite family of parameters.
It is constructed inside the complex numbers from the literal splitting
polynomial. Its row characters have exactly the sixth-power kernel. -/
namespace ArtinMatthews
open Polynomial
open scoped Classical
noncomputable section
variable {F : Type*} [Field F] [Algebra F ℂ]

def sixthKummerRowPolynomial (A : Finset F) : F[X] :=
  (X^6-1) * ∏ a ∈ A, (X^6-C a)

def sixthKummerRowField (A : Finset F) : IntermediateField F ℂ :=
  IntermediateField.adjoin F ((sixthKummerRowPolynomial A).rootSet ℂ)

omit [Algebra F ℂ] in
theorem sixthKummerRowPolynomial_ne_zero (A : Finset F) : sixthKummerRowPolynomial A ≠ 0 := by
  apply mul_ne_zero
  · simpa only [map_one] using (X_pow_sub_C_ne_zero (by norm_num : 0 < 6) (1:F))
  · exact Finset.prod_ne_zero_iff.mpr fun a _ => X_pow_sub_C_ne_zero (by norm_num) a

theorem mem_sixthKummerRowPolynomial_rootSet (A : Finset F) (z : ℂ) :
    z ∈ (sixthKummerRowPolynomial A).rootSet ℂ ↔
      z^6 = 1 ∨ ∃ a ∈ A, z^6 = algebraMap F ℂ a := by
  rw [Polynomial.mem_rootSet_of_ne (sixthKummerRowPolynomial_ne_zero A)]
  simp only [sixthKummerRowPolynomial,map_mul,map_sub,map_pow,map_one,aeval_X,
    map_prod,aeval_C,mul_eq_zero,sub_eq_zero,Finset.prod_eq_zero_iff]

def complexSixthRoot (a : F) : ℂ :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap F ℂ a) (by norm_num : 0 < 6)).choose

theorem complexSixthRoot_pow (a : F) : (complexSixthRoot a)^6 = algebraMap F ℂ a :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap F ℂ a) (by norm_num : 0 < 6)).choose_spec

theorem complexSixthRoot_mem (A : Finset F) (a : F) (ha : a ∈ A) :
    complexSixthRoot a ∈ sixthKummerRowField A :=
  IntermediateField.subset_adjoin F _
    ((mem_sixthKummerRowPolynomial_rootSet A _).mpr (Or.inr ⟨a,ha,complexSixthRoot_pow a⟩))

def sixthKummerRowRoot (A : Finset F) (a : F) (ha : a ∈ A) : sixthKummerRowField A :=
  ⟨complexSixthRoot a,complexSixthRoot_mem A a ha⟩

theorem sixthKummerRowRoot_pow (A : Finset F) (a : F) (ha : a ∈ A) :
    (sixthKummerRowRoot A a ha)^6 = algebraMap F (sixthKummerRowField A) a := by
  apply Subtype.ext
  exact complexSixthRoot_pow a

theorem sixthKummerRowRoot_ne_zero (A : Finset F) (a : F) (ha : a ∈ A) (ha0 : a ≠ 0) :
    sixthKummerRowRoot A a ha ≠ 0 := by
  intro hz
  have H := sixthKummerRowRoot_pow A a ha
  rw [hz,zero_pow (by decide : 6 ≠ 0)] at H
  exact ha0 ((algebraMap F (sixthKummerRowField A)).injective (by simpa using H.symm))

instance sixthKummerRowField_isSplittingField (A : Finset F) :
    IsSplittingField F (sixthKummerRowField A) (sixthKummerRowPolynomial A) :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

instance sixthKummerRowField_finiteDimensional (A : Finset F) :
    FiniteDimensional F (sixthKummerRowField A) :=
  IsSplittingField.finiteDimensional _ (sixthKummerRowPolynomial A)

instance sixthKummerRowField_normal (A : Finset F) : Normal F (sixthKummerRowField A) :=
  Normal.of_isSplittingField (sixthKummerRowPolynomial A)

instance sixthKummerRowField_isGalois [CharZero F] (A : Finset F) :
    IsGalois F (sixthKummerRowField A) where

instance sixthKummerRowField_numberField [NumberField F] (A : Finset F) :
    NumberField (sixthKummerRowField A) :=
  NumberField.of_module_finite F (sixthKummerRowField A)

theorem sixthKummerRowGenerator_pow (A : Finset F) {z : ℂ}
    (hz : z ∈ (sixthKummerRowPolynomial A).rootSet ℂ) :
    ∃ a : F, (⟨z,IntermediateField.subset_adjoin F _ hz⟩ : sixthKummerRowField A)^6 =
      algebraMap F (sixthKummerRowField A) a := by
  rcases (mem_sixthKummerRowPolynomial_rootSet A z).mp hz with h | ⟨a,_ha,h⟩
  · refine ⟨1,?_⟩
    apply Subtype.ext
    simpa only [map_one,IntermediateField.coe_pow,IntermediateField.coe_one,Subtype.coe_mk] using h
  · exact ⟨a,Subtype.ext h⟩

theorem sixthKummerRowField_aut_commute {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (A : Finset F) (σ τ : Gal(sixthKummerRowField A/F)) : σ*τ = τ*σ := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.adjoin_algHom_ext F
  intro z hz
  let x : sixthKummerRowField A := ⟨z,IntermediateField.subset_adjoin F _ hz⟩
  change σ (τ x) = τ (σ x)
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨a,ha⟩ := sixthKummerRowGenerator_pow A hz
  have H : radicalAutCharacter hζ ha hx (σ*τ) = radicalAutCharacter hζ ha hx (τ*σ) := by
    rw [map_mul,map_mul,mul_comm]
  have HR := congrArg (fun w : rootsOfUnity 6 (sixthKummerRowField A) =>
    ((w : (sixthKummerRowField A)ˣ) : sixthKummerRowField A)) H
  change σ (τ x) / x = τ (σ x) / x at HR
  exact (div_left_inj' hx).mp HR

theorem sixthKummerRowField_isAbelianGalois [CharZero F] {ζ : F}
    (hζ : IsPrimitiveRoot ζ 6) (A : Finset F) :
    IsAbelianGalois F (sixthKummerRowField A) := by
  let : IsMulCommutative Gal(sixthKummerRowField A/F) :=
    .of_comm (sixthKummerRowField_aut_commute hζ A)
  exact {}

def sixthKummerRootUnityComplex (A : Finset F) :
    rootsOfUnity 6 (sixthKummerRowField A) →* ℂˣ :=
  (Units.map (sixthKummerRowField A).val.toRingHom.toMonoidHom).comp (Subgroup.subtype _)

theorem sixthKummerRootUnityComplex_injective (A : Finset F) :
    Function.Injective (sixthKummerRootUnityComplex A) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  apply (sixthKummerRowField A).val.injective
  exact congrArg (fun z : ℂˣ => (z:ℂ)) h

def sixthKummerRowCharacter {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (A : Finset F) (a : F) (ha : a ∈ A) (ha0 : a ≠ 0) :
    Gal(sixthKummerRowField A/F) →* ℂˣ :=
  (sixthKummerRootUnityComplex A).comp
    (radicalAutCharacter hζ (sixthKummerRowRoot_pow A a ha) (sixthKummerRowRoot_ne_zero A a ha ha0))

theorem sixthKummerRowCharacter_eq_iff_exists_sixthPower [CharZero F] {ζ : F}
    (hζ : IsPrimitiveRoot ζ 6) (A : Finset F)
    (a b : F) (ha : a ∈ A) (hb : b ∈ A) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    sixthKummerRowCharacter hζ A a ha ha0 = sixthKummerRowCharacter hζ A b hb hb0 ↔
      ∃ t : F, t^6 = a/b := by
  have he : sixthKummerRowCharacter hζ A a ha ha0 = sixthKummerRowCharacter hζ A b hb hb0 ↔
      radicalAutCharacter hζ (sixthKummerRowRoot_pow A a ha) (sixthKummerRowRoot_ne_zero A a ha ha0) =
        radicalAutCharacter hζ (sixthKummerRowRoot_pow A b hb) (sixthKummerRowRoot_ne_zero A b hb hb0) := by
    constructor
    · intro h
      apply MonoidHom.ext
      intro σ
      exact sixthKummerRootUnityComplex_injective A (DFunLike.congr_fun h σ)
    · intro h
      unfold sixthKummerRowCharacter
      rw [h]
  rw [he]
  exact radicalAutCharacter_eq_iff_exists_pow hζ
    (sixthKummerRowRoot_pow A a ha) (sixthKummerRowRoot_ne_zero A a ha ha0)
    (sixthKummerRowRoot_pow A b hb) (sixthKummerRowRoot_ne_zero A b hb hb0)

theorem sixthKummerRowCharacter_one_iff_exists_sixthPower [CharZero F] {ζ : F}
    (hζ : IsPrimitiveRoot ζ 6) (A : Finset F) (a : F) (ha : a ∈ A) (ha0 : a ≠ 0) :
    sixthKummerRowCharacter hζ A a ha ha0 = 1 ↔ ∃ t : F, t^6 = a := by
  have he : sixthKummerRowCharacter hζ A a ha ha0 = 1 ↔
      radicalAutCharacter hζ (sixthKummerRowRoot_pow A a ha)
        (sixthKummerRowRoot_ne_zero A a ha ha0) = 1 := by
    constructor
    · intro h
      apply MonoidHom.ext
      intro σ
      apply sixthKummerRootUnityComplex_injective A
      simpa only [sixthKummerRowCharacter,MonoidHom.comp_apply,MonoidHom.one_apply,map_one]
        using DFunLike.congr_fun h σ
    · intro h
      unfold sixthKummerRowCharacter
      rw [h]
      apply MonoidHom.ext
      intro σ
      simp only [MonoidHom.comp_apply,MonoidHom.one_apply,map_one]
  exact he.trans (radicalAutCharacter_one_iff_exists_pow hζ
    (sixthKummerRowRoot_pow A a ha) (sixthKummerRowRoot_ne_zero A a ha ha0))

end
end ArtinMatthews
