module

public import ArtinMatthews.VaryingKummerAnalyticIdealTraceCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ideal-quotient Gauss sums for arbitrary number fields. The additive
character is constructed from the trace dual; primitive finite-ring Fourier
identities are reused from the checked OpenAI proof. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (M : Ideal (𝓞 K)) [NeZero M]
local notation "hM" => (NeZero.ne M)

local instance idealGaussQuotientFinite : Finite ((𝓞 K) ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient hM
local instance idealGaussQuotientFintype : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _

theorem idealQuotient_card_eq_absNorm : Fintype.card ((𝓞 K) ⧸ M) = Ideal.absNorm M := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

def idealTraceGaussSum (χ : MulChar ((𝓞 K) ⧸ M) ℂ) : ℂ :=
  gaussSum χ (idealTraceAddChar K M hM)

theorem idealTraceGaussSum_mul_conjugate (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    idealTraceGaussSum K M χ * star (idealTraceGaussSum K M χ) =
      (Ideal.absNorm M : ℂ) := by
  simpa only [idealTraceGaussSum, idealQuotient_card_eq_absNorm K M] using
    primitive_gaussSum_mul_conjugate χ hχ (idealTraceAddChar K M hM)
      (idealTraceAddChar_isPrimitive K M hM)

theorem idealTraceGaussSum_norm_sq (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖idealTraceGaussSum K M χ‖ ^ 2 = (Ideal.absNorm M : ℝ) := by
  simpa only [idealTraceGaussSum, idealQuotient_card_eq_absNorm K M] using
    primitive_gaussSum_norm_sq χ hχ (idealTraceAddChar K M hM)
      (idealTraceAddChar_isPrimitive K M hM)

theorem idealTraceGaussSum_norm (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖idealTraceGaussSum K M χ‖ = Real.sqrt (Ideal.absNorm M : ℝ) := by
  simpa only [idealTraceGaussSum, idealQuotient_card_eq_absNorm K M] using
    primitive_gaussSum_norm χ hχ (idealTraceAddChar K M hM)
      (idealTraceAddChar_isPrimitive K M hM)

theorem idealTraceGaussSum_ne_zero (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : idealTraceGaussSum K M χ ≠ 0 :=
  primitive_gaussSum_ne_zero χ hχ (idealTraceAddChar K M hM)
    (idealTraceAddChar_isPrimitive K M hM)

def idealTraceRootNumber (χ : MulChar ((𝓞 K) ⧸ M) ℂ) : ℂ :=
  idealTraceGaussSum K M χ / (Real.sqrt (Ideal.absNorm M : ℝ) : ℂ)

theorem idealTraceRootNumber_norm (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : ‖idealTraceRootNumber K M χ‖ = 1 := by
  have hn : 0 < (Ideal.absNorm M : ℝ) := by
    rw [← idealQuotient_card_eq_absNorm K M]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ((𝓞 K) ⧸ M))
  rw [idealTraceRootNumber, norm_div, idealTraceGaussSum_norm K M χ hχ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_self (Real.sqrt_ne_zero'.mpr hn)

theorem idealTraceFourier_inversion (f : ((𝓞 K) ⧸ M) → ℂ) (x : (𝓞 K) ⧸ M) :
    (∑ a, transform (idealTraceAddChar K M hM) f a *
      idealTraceAddChar K M hM (-(a*x))) = (Ideal.absNorm M : ℂ) * f x := by
  simpa only [idealQuotient_card_eq_absNorm K M] using
    transform_inversion (idealTraceAddChar K M hM)
      (idealTraceAddChar_isPrimitive K M hM) f x

theorem idealTraceFourier_primitive (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : (𝓞 K) ⧸ M) :
    (∑ b, χ b * idealTraceAddChar K M hM (a*b)) =
      χ⁻¹ a * idealTraceGaussSum K M χ :=
  transform_primitive_character χ hχ (idealTraceAddChar K M hM) a

theorem idealTraceFourier_character_expansion (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : (𝓞 K) ⧸ M) :
    χ a = (∑ b, χ⁻¹ b * idealTraceAddChar K M hM (a*b)) /
      idealTraceGaussSum K M χ⁻¹ :=
  primitive_character_expansion χ hχ (idealTraceAddChar K M hM)
    (idealTraceAddChar_isPrimitive K M hM) a

end
end ArtinMatthews.VaryingKummerAnalytic
