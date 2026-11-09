module

public import ArtinMatthews.VaryingKummerAnalyticDedekindSeriesPartialComplex


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine finite-order ray characters over arbitrary number fields.
The algebraic character data and coefficient bounds are extracted from
OpenAI PrimePackets/RayCharacter.lean; the analytic development below uses
the proved arbitrary-signature ideal series, with no totally-real premise. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Set Filter
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

def rationalModulusIdeal (R : Type*) [CommRing R] (N : ℕ) : Ideal R := Ideal.span {(N : R)}

def integralIdealFractionalUnit {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr hI)

@[simp] theorem integralIdealFractionalUnit_top {K : Type*} [Field K] [NumberField K] :
    integralIdealFractionalUnit (⊤ : Ideal (𝓞 K)) top_ne_bot = 1 := by
  apply Units.ext
  simp [integralIdealFractionalUnit]

lemma quotient_isUnit_iff_span_coprime {R : Type*} [CommRing R]
    (M : Ideal R) (a : R) :
    IsUnit (Ideal.Quotient.mk M a) ↔ IsCoprime (Ideal.span {a}) M := by
  rw [Ideal.isCoprime_iff_sup_eq]
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have he : a * b - 1 ∈ M := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp only [map_sub, map_mul, map_one, hb, sub_self]
    apply (Ideal.eq_top_iff_one _).mpr
    have hmem : a * b ∈ Ideal.span {a} ⊔ M :=
      Submodule.mem_sup_left (Ideal.mem_span_singleton.mpr (dvd_mul_right a b))
    have hm : a * b - 1 ∈ Ideal.span {a} ⊔ M := Submodule.mem_sup_right he
    simpa only [sub_sub_cancel] using (Ideal.span {a} ⊔ M).sub_mem hmem hm
  · intro h
    have h1 : (1 : R) ∈ Ideal.span {a} ⊔ M := by rw [h]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk M b, ?_⟩
    have he := congrArg (Ideal.Quotient.mk M) hxy
    simpa only [map_add, map_mul, map_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero] using he

variable {K : Type*} [Field K] [NumberField K]

 

structure EvenRayCharacter (K : Type*) [Field K] [NumberField K] (N : ℕ) where
  idealHom : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* ℂˣ
  finiteOrder : ∃ e : ℕ, 0 < e ∧ ∀ J, idealHom J ^ e = 1
  residue : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ
  principalLaw : ∀ (a : 𝓞 K) (ha : a ≠ 0),
    IsCoprime (Ideal.span {a}) (rationalModulusIdeal (𝓞 K) N) →
    (idealHom (integralIdealFractionalUnit (Ideal.span {a})
      (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha)) : ℂ) =
        residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a)

namespace EvenRayCharacter
variable {N : ℕ} (ψ : EvenRayCharacter K N)

lemma idealHom_norm (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ‖(ψ.idealHom J : ℂ)‖ = 1 := by
  obtain ⟨e, he, hpow⟩ := ψ.finiteOrder
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) he.ne').mp
  have H := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) (hpow J)
  simpa only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] using H

 

lemma residue_unit (z : (𝓞 K)ˣ) :
    ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z : 𝓞 K)) = 1 := by
  have hspan : Ideal.span {(z : 𝓞 K)} = ⊤ := Ideal.span_singleton_eq_top.mpr z.isUnit
  have hcop : IsCoprime (Ideal.span {(z : 𝓞 K)}) (rationalModulusIdeal (𝓞 K) N) := by
    rw [hspan, ← Ideal.one_eq_top]
    exact isCoprime_one_left
  have H := ψ.principalLaw (z : 𝓞 K) z.ne_zero hcop
  simpa only [hspan, integralIdealFractionalUnit_top, map_one, Units.val_one] using H.symm

 

def underlyingIdeal (J : integralFractionalIdeals K) : Ideal (𝓞 K) :=
  ((integralFractionalIdealsEquiv K).symm J).val

lemma underlyingIdeal_ne_bot (J : integralFractionalIdeals K) :
    underlyingIdeal J ≠ ⊥ := ((integralFractionalIdealsEquiv K).symm J).property

lemma underlyingIdeal_coe (J : integralFractionalIdeals K) :
    (underlyingIdeal J : FractionalIdeal (𝓞 K)⁰ K) = J.val.val := by
  have H := (integralFractionalIdealsEquiv K).apply_symm_apply J
  exact congrArg (fun U : integralFractionalIdeals K => U.val.val) H

lemma underlyingIdeal_unit (J : integralFractionalIdeals K) :
    integralIdealFractionalUnit (underlyingIdeal J) (underlyingIdeal_ne_bot J) = J.val := by
  apply Units.ext
  exact underlyingIdeal_coe J

 

def coefficient (J : integralFractionalIdeals K) : ℂ :=
  if IsCoprime (underlyingIdeal J) (rationalModulusIdeal (𝓞 K) N)
  then (ψ.idealHom J.val : ℂ) else 0

lemma coefficient_norm_le_one (J : integralFractionalIdeals K) :
    ‖ψ.coefficient J‖ ≤ 1 := by
  classical
  unfold coefficient
  split_ifs
  · exact (ψ.idealHom_norm J.val).le
  · simp only [norm_zero, zero_le_one]

 

def dirichlet (s : ℂ) : ℂ :=
  ∑' J : integralFractionalIdeals K,
    ψ.coefficient J * ((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)^(-s)

lemma dirichlet_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : integralFractionalIdeals K =>
      ψ.coefficient J * ((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)^(-s)) := by
  apply Summable.of_norm_bounded (integralFractionalIdeals_norm_summable hs)
  intro J
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos _),
    Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)
    (ψ.coefficient_norm_le_one J)


end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
