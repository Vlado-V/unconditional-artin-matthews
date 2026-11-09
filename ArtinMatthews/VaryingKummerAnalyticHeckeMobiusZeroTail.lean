module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusZeroPower


set_option backward.privateInPublic true
@[expose] public section

/-! A zero in the manuscript rectangle forces a genuinely large smoothed
Möbius tail. The large-U threshold is constructed from the proved negative
power and is independent of the character and conductor. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open scoped NumberField nonZeroDivisors Classical
noncomputable section

namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}

def mobiusSmoothedTail (ψ : EvenIdealRayCharacter K M) (D : ℝ) (ρ : ℂ) (Y : ℝ) : ℂ :=
  ∑' I : Ideal (𝓞 K), if D < (Ideal.absNorm I : ℝ) then
    ψ.mobiusConvolutionCoefficient D I*(Ideal.absNorm I : ℂ)^(-ρ)*
      Complex.exp (-(Ideal.absNorm I : ℂ)/(Y : ℂ)) else 0

end EvenIdealRayCharacter

theorem norm_mobius_unit_ge_half {Y : ℝ} (hY : 2 ≤ Y) :
    (1/2 : ℝ) ≤ ‖Complex.exp (-1/(Y : ℂ))‖ := by
  have he : (-1/(Y : ℂ)) = ((-1/Y : ℝ) : ℂ) := by push_cast; ring
  rw [he,Complex.norm_exp,Complex.ofReal_re]
  have hi : 1/Y ≤ (1/2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hY
  have hexp := Real.add_one_le_exp (-1/Y)
  rw [neg_div] at hexp
  rw [neg_div]
  linarith

theorem exists_actual_zero_large_mobius_tail
    (K : Type*) [Field K] [NumberField K] :
    ∃ r U₀ : ℝ, 0 < r ∧ r < 1/10 ∧ 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
        (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
        (_hnp : ψ.IsNonprincipal), (Ideal.absNorm M : ℝ) ≤ U →
        ∀ ρ : ℂ, (249/250 : ℝ) ≤ ρ.re → |ρ.im| ≤ 4*U^r →
          ψ.primitiveContinued hM hprim ρ=0 →
          1/4 ≤ ‖ψ.mobiusSmoothedTail (U^2) ρ (U^10)‖ := by
  obtain ⟨r,U₀,hr,hr',hU₀,hbound⟩ := exists_actual_mobius_zero_detector_eventually_small K
  refine ⟨r,U₀,hr,hr',hU₀,?_⟩
  intro U hU M ψ hM hprim hnp hMU ρ hρ him hz
  have hU2 : 2 ≤ U := hU₀.trans hU
  have hU1 : 1 ≤ U := by linarith
  have hY : 2 ≤ U^10 := by
    have H := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hU2 10
    norm_num at H
    linarith
  have hu := norm_mobius_unit_ge_half hY
  have hs := hbound U hU ψ hM hprim hnp hMU ρ hρ him hz
  have he := ψ.mobiusSmoothedSum_unit_tail hM hprim hnp (D := U^2) (one_le_pow₀ hU1)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hY) (by linarith : -1 < ρ.re)
  change ψ.mobiusSmoothedSum (U^2) ρ (U^10) = Complex.exp (-1/((U^10 : ℝ) : ℂ)) +
    ψ.mobiusSmoothedTail (U^2) ρ (U^10) at he
  have hsub : ψ.mobiusSmoothedSum (U^2) ρ (U^10) - ψ.mobiusSmoothedTail (U^2) ρ (U^10) =
      Complex.exp (-1/((U^10 : ℝ) : ℂ)) := by rw [he]; ring
  have H := norm_sub_le (ψ.mobiusSmoothedSum (U^2) ρ (U^10)) (ψ.mobiusSmoothedTail (U^2) ρ (U^10))
  rw [hsub] at H
  linarith

end
end ArtinMatthews.VaryingKummerAnalytic
