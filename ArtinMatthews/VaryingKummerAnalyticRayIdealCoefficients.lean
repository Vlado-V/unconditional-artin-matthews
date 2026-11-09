module

public import ArtinMatthews.VaryingKummerAnalyticRaySeries
public import Mathlib.NumberTheory.NumberField.Ideal.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Actual integral-generator residue weights and their equality with the
frozen arbitrary-field ray character coefficients. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField FractionalIdeal Set Filter
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
variable {K : Type*} [Field K] [NumberField K]

def idealIntegerElement (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) : 𝓞 K :=
  ((FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp a.property).choose

lemma idealIntegerElement_coe (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) :
    (idealIntegerElement I hI a : K) = (a.val:K) :=
  ((FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp a.property).choose_spec.2

lemma idealIntegerElement_unitAction (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) (z : (𝓞 K)ˣ) :
    idealIntegerElement I hI (idealElementUnitAction _ z a) =
      (z:𝓞 K)*idealIntegerElement I hI a := by
  apply NumberField.RingOfIntegers.coe_injective
  simp only [idealIntegerElement_coe,map_mul]
  rfl

def idealResidueElementWeight (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) : ℂ :=
  χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (idealIntegerElement I hI a))

lemma idealResidueElementWeight_unitAction (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) (z : (𝓞 K)ˣ) :
    idealResidueElementWeight I hI N χ (idealElementUnitAction _ z a) =
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) *
        idealResidueElementWeight I hI N χ a := by
  simp only [idealResidueElementWeight,idealIntegerElement_unitAction,map_mul]

def idealResidueCoefficient (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) : ℂ :=
  idealResidueElementWeight I hI N χ (idealElementRepresentative _ J)

 

lemma idealResidueCoefficient_eq_of_generator (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) :
    idealResidueCoefficient I hI N χ (relativeElementClassMap _ a) =
      idealResidueElementWeight I hI N χ a := by
  obtain ⟨z,hz,_⟩ := exists_unique_unit_of_relativeElementClassMap_eq _
    (idealElementRepresentative _ (relativeElementClassMap _ a)) a
    (idealElementRepresentative_spec _ _)
  conv_rhs => rw [← hz,idealResidueElementWeight_unitAction,hunit,one_mul]
  rfl

lemma finiteMulChar_norm_le_one {R : Type*} [CommRing R] [Finite R]
    (χ : MulChar R ℂ) (a : R) : ‖χ a‖ ≤ 1 := by
  classical
  by_cases h : IsUnit a
  · obtain ⟨z,rfl⟩ := h
    have H : ‖χ (z:R)‖ = 1 := by
      refine (pow_eq_one_iff_of_nonneg (norm_nonneg _)
        (Nat.card_pos (α := Rˣ)).ne').mp ?_
      rw [← norm_pow,← map_pow,← Units.val_pow_eq_pow_val,pow_card_eq_one',
        Units.val_one,map_one,norm_one]
    exact H.le
  · rw [χ.map_nonunit h,norm_zero]
    exact zero_le_one

lemma idealResidueElementWeight_norm_le_one (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) :
    ‖idealResidueElementWeight I hI N χ a‖ ≤ 1 := by
  have hmod : rationalModulusIdeal (𝓞 K) N ≠ ⊥ := by
    change Ideal.span {(N : 𝓞 K)} ≠ ⊥
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using
      (Nat.cast_ne_zero.mpr (NeZero.ne N) : (N : 𝓞 K) ≠ 0)
  let : Finite ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) :=
    Ring.HasFiniteQuotients.finiteQuotient hmod
  exact finiteMulChar_norm_le_one χ _

lemma idealResidueCoefficient_summable (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : integralIdealClassFiber (integralIdealFractionalUnit I hI) =>
      idealResidueCoefficient I hI N χ J *
        ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ)^(-s)) := by
  apply (mixedPartialDedekind_norm_summable K (integralIdealFractionalUnit I hI) hs).of_norm_bounded
  intro J
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos _),
    Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)
    (idealResidueElementWeight_norm_le_one I hI N χ _)

namespace EvenRayCharacter
variable {N : ℕ} (ψ : EvenRayCharacter K N)

lemma generator_principal_product (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    Ideal.span {idealIntegerElement I hI (idealElementRepresentative _ J)} =
      I * underlyingIdeal ⟨J.val, J.property.1⟩ := by
  let U := integralIdealFractionalUnit I hI
  have h := congrArg Subtype.val (idealElementRepresentative_spec U J)
  change relativeElementIdeal U (idealElementRepresentative U J).val = J.val at h
  have hm : J.val * U = toPrincipalIdeal (𝓞 K) K (idealElementRepresentative U J).val := by
    rw [← h]
    simp [relativeElementIdeal]
  apply FractionalIdeal.coeIdeal_injective (K := K)
  change (Ideal.span {idealIntegerElement I hI (idealElementRepresentative U J)} :
    FractionalIdeal (𝓞 K)⁰ K) = ((I * underlyingIdeal ⟨J.val, J.property.1⟩ : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  have he : algebraMap (𝓞 K) K
      (idealIntegerElement I hI (idealElementRepresentative U J)) =
      ((idealElementRepresentative U J).val : K) := idealIntegerElement_coe I hI _
  rw [he]
  have H := congrArg (fun W : (FractionalIdeal (𝓞 K)⁰ K)ˣ => W.val) hm
  simp only [Units.val_mul, coe_toPrincipalIdeal] at H
  exact H.symm.trans (by erw [underlyingIdeal_coe]; exact mul_comm _ _)

lemma generator_integer_ne_zero (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    idealIntegerElement I hI (idealElementRepresentative _ J) ≠ 0 := by
  intro hz
  have H := idealIntegerElement_coe I hI (idealElementRepresentative _ J)
  rw [hz] at H
  change (0 : K) = _ at H
  exact (idealElementRepresentative _ J).val.ne_zero H.symm

lemma generator_fractional_product (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    integralIdealFractionalUnit
      (Ideal.span {idealIntegerElement I hI (idealElementRepresentative _ J)})
      (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using
        generator_integer_ne_zero I hI J) = integralIdealFractionalUnit I hI * J.val := by
  apply Units.ext
  change (Ideal.span {idealIntegerElement I hI (idealElementRepresentative _ J)} :
    FractionalIdeal (𝓞 K)⁰ K) = _
  erw [generator_principal_product, FractionalIdeal.coeIdeal_mul, underlyingIdeal_coe]
  rfl

 

lemma coefficient_eq_residue (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hcop : IsCoprime I (rationalModulusIdeal (𝓞 K) N))
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    ψ.coefficient ⟨J.val, J.property.1⟩ =
      ((ψ.idealHom (integralIdealFractionalUnit I hI) : ℂ))⁻¹ *
        idealResidueCoefficient I hI N ψ.residue J := by
  let a := idealIntegerElement I hI (idealElementRepresentative _ J)
  have hid : idealResidueCoefficient I hI N ψ.residue J =
      ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) := rfl
  have hc : IsCoprime (Ideal.span {a}) (rationalModulusIdeal (𝓞 K) N) ↔
      IsCoprime (underlyingIdeal ⟨J.val, J.property.1⟩) (rationalModulusIdeal (𝓞 K) N) := by
    rw [show Ideal.span {a} = I * underlyingIdeal ⟨J.val, J.property.1⟩ from
      generator_principal_product I hI J, IsCoprime.mul_left_iff, and_iff_right hcop]
  change (if IsCoprime (underlyingIdeal ⟨J.val, J.property.1⟩)
    (rationalModulusIdeal (𝓞 K) N) then (ψ.idealHom J.val : ℂ) else 0) = _
  erw [hid]
  by_cases hJ : IsCoprime (underlyingIdeal ⟨J.val, J.property.1⟩)
      (rationalModulusIdeal (𝓞 K) N)
  · rw [ite_eq_left hJ, ← ψ.principalLaw a (generator_integer_ne_zero I hI J) (hc.mpr hJ),
      generator_fractional_product, map_mul, Units.val_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
  · rw [ite_eq_right hJ, ψ.residue.map_nonunit
      (fun hunit => hJ (hc.mp ((quotient_isUnit_iff_span_coprime _ a).mp hunit))), mul_zero]

 

/-- The actual finite-order ray character is invariant under the full unit
orbit; this is proved from its principal law, rather than assumed. -/
theorem idealResidueElementWeight_invariant (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) (z : (𝓞 K)ˣ) :
    idealResidueElementWeight I hI N ψ.residue (idealElementUnitAction _ z a) =
      idealResidueElementWeight I hI N ψ.residue a := by
  rw [idealResidueElementWeight_unitAction, ψ.residue_unit, one_mul]

theorem residueCoefficient_eq_of_generator (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) :
    idealResidueCoefficient I hI N ψ.residue (relativeElementClassMap _ a) =
      idealResidueElementWeight I hI N ψ.residue a :=
  idealResidueCoefficient_eq_of_generator I hI N ψ.residue ψ.residue_unit a

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic

