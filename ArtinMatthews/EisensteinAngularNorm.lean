module

public import ArtinMatthews.EisensteinAngularIdeal
public import ArtinMatthews.NormPrincipalCongruence
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization


set_option backward.privateInPublic true
@[expose] public section

/-! Pull the genuine Eisenstein angular ideal character back by the
relative ideal norm. The principal congruence and unitarity off three
are derived from actual integral norms. -/
namespace ArtinMatthews.AngularLambda
open OAI OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.ConcreteTraceCRT
open NumberField
open scoped NumberField Classical
noncomputable section

local instance : IsCyclotomicExtension {3} ℚ BaseField :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsPrincipalIdealRing BaseIntegers :=
  IsCyclotomicExtension.Rat.three_pid BaseField

variable (F : Type*) [Field F] [NumberField F] [Algebra BaseField F]

def angularNormIdeal : Ideal (𝓞 F) →*₀ ℂ :=
  eisensteinAngularIdeal.comp (Ideal.relNorm BaseIntegers)

theorem angularNormIdeal_apply (I : Ideal (𝓞 F)) :
    angularNormIdeal F I = eisensteinAngularIdeal (Ideal.relNorm BaseIntegers I) := rfl

theorem integralNorm_sub_one_dvd (a : 𝓞 F) (ha : (3 : 𝓞 F) ∣ a-1) :
    (3 : BaseIntegers) ∣ Algebra.intNorm BaseIntegers (𝓞 F) a-1 := by
  rw [Algebra.intNorm_eq_norm]
  apply norm_sub_one_dvd_of_sub_one_dvd
  simpa only [map_ofNat] using ha

theorem angularNormIdeal_principal (a : 𝓞 F) (ha : a ≠ 0)
    (hthree : (3 : 𝓞 F) ∣ a-1) :
    angularNormIdeal F (Ideal.span {a}) =
      complexAngular (eisEmbedding (Algebra.intNorm BaseIntegers (𝓞 F) a)) := by
  rw [angularNormIdeal_apply,Ideal.relNorm_singleton]
  apply eisensteinAngularIdeal_principal
  · rw [Algebra.intNorm_eq_norm]
    exact Algebra.norm_ne_zero_iff.mpr ha
  · exact integralNorm_sub_one_dvd F a hthree

theorem relativeNorm_coprime_three (I : Ideal (𝓞 F))
    (hc : IsCoprime I (Ideal.span {(3 : 𝓞 F)})) :
    IsCoprime (Ideal.relNorm BaseIntegers I) (Ideal.span {(3 : BaseIntegers)}) := by
  obtain ⟨a,ha,b,hb,hab⟩ := Ideal.isCoprime_iff_exists.mp hc
  have hadiv : (3 : 𝓞 F) ∣ a-1 := by
    have hbdiv := Ideal.mem_span_singleton.mp hb
    have he : a-1 = -b := by linear_combination hab
    rw [he]
    exact dvd_neg.mpr hbdiv
  have hn := integralNorm_sub_one_dvd F a hadiv
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨Algebra.intNorm BaseIntegers (𝓞 F) a,?_,
    1-Algebra.intNorm BaseIntegers (𝓞 F) a,?_,by ring⟩
  · rw [Algebra.intNorm_eq_norm]
    exact Ideal.norm_mem_relNorm BaseIntegers I ha
  · apply Ideal.mem_span_singleton.mpr
    convert dvd_neg.mpr hn using 1; ring

theorem angularNormIdeal_norm (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (hc : IsCoprime I (Ideal.span {(3 : 𝓞 F)})) : ‖angularNormIdeal F I‖ = 1 := by
  rw [angularNormIdeal_apply]
  apply eisensteinAngularIdeal_norm_of_coprime
  · exact Ideal.relNorm_eq_bot_iff.not.mpr hI
  · have hn := relativeNorm_coprime_three F I hc
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hn.sup_eq]
    apply sup_le_sup_left
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply Ideal.mem_span_singleton.mpr
    exact (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three

end
end ArtinMatthews.AngularLambda
