module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealConjugation


set_option backward.privateInPublic true
@[expose] public section

/-! Conjugation of the actual mixed archimedean factor and a positively
scaled primitive completion. The identities hold at every complex argument
with Mathlib's total Gamma convention. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped NumberField nonZeroDivisors Classical ComplexConjugate
noncomputable section

theorem positiveReal_cpow_conj {A : ℝ} (hA : 0 < A) (s : ℂ) :
    (A:ℂ)^(conj s) = conj ((A:ℂ)^s) := by
  have ha : (A:ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hA.le]
    exact ne_of_lt Real.pi_pos
  simpa only [Complex.conj_ofReal] using Complex.cpow_conj (A:ℂ) s ha

theorem mixedGammaFactor_conj (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    mixedGammaFactor K (conj s) = conj (mixedGammaFactor K s) := by
  unfold mixedGammaFactor
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro w _
  have he : (InfinitePlace.mult w:ℂ)*conj s/2 =
      conj ((InfinitePlace.mult w:ℂ)*s/2) := by
    simp only [map_div₀,map_mul,map_natCast,map_ofNat]
  rw [he,Complex.Gamma_conj,← map_neg,positiveReal_cpow_conj Real.pi_pos]
  simp only [map_mul,map_div₀,map_one,map_ofNat]

namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hnp : ψ.IsNonprincipal)
include hnp

/-- Any positive conductor normalization retains the proved conjugation law. -/
theorem scaledGammaPrimitive_inverse_conj {A : ℝ} (hA : 0 < A) (s : ℂ) :
    (A:ℂ)^(conj s) * mixedGammaFactor K (conj s) *
      ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) (conj s) =
    conj ((A:ℂ)^s * mixedGammaFactor K s * ψ.primitiveContinued hM hprim s) := by
  rw [positiveReal_cpow_conj hA,mixedGammaFactor_conj,
    ψ.primitiveContinued_inverse_conj hM hprim hnp]
  simp only [map_mul]

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
