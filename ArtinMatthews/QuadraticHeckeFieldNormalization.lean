module

public import ArtinMatthews.QuadraticHeckeDualGamma
public import ArtinMatthews.VaryingKummerAnalyticMixedConductorNormalization
public import ArtinMatthews.VaryingKummerAnalyticMixedZetaFunctionalEquation


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section

variable (K : Type) [Field K] [NumberField K]
local notation "r" => InfinitePlace.nrComplexPlaces K

/-- The fixed field scale, with the conductor norm kept separate. -/
def quadraticHeckeFieldScale : ℝ :=
  mixedDiscriminantScale K / Real.pi ^ r

theorem quadraticHeckeFieldScale_pos : 0 < quadraticHeckeFieldScale K :=
  div_pos (mixedDiscriminantScale_pos K) (pow_pos Real.pi_pos _)

private theorem quadraticHeckeGammaAtom_ratio (s : ℂ) :
    mixedGammaAtom s * (mixedGammaAtom (1 - s))⁻¹ =
      (Real.pi : ℂ) ^ (-(2 * s - 1)) * (Complex.Gamma s / Complex.Gamma (1 - s)) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp : (Real.pi : ℂ) ^ (-s) * ((Real.pi : ℂ) ^ (-(1 - s)))⁻¹ =
      (Real.pi : ℂ) ^ (-(2 * s - 1)) := by
    rw [← Complex.cpow_neg, neg_neg, ← Complex.cpow_add _ _ hπ]
    congr 1
    ring
  simp only [mixedGammaAtom, mul_inv_rev, div_eq_mul_inv]
  calc
    _ = ((Real.pi : ℂ) ^ (-s) * ((Real.pi : ℂ) ^ (-(1 - s)))⁻¹) *
        (Complex.Gamma s * (Complex.Gamma (1 - s))⁻¹) := by ring
    _ = _ := by rw [hp]

private theorem quadraticHeckeFieldScale_exp (z : ℂ) :
    Complex.exp (z * (Real.log (quadraticHeckeFieldScale K) : ℂ)) =
      (mixedDiscriminantScale K : ℂ) ^ z * ((Real.pi : ℂ) ^ (-z)) ^ r := by
  rw [positiveReal_cpow_eq_exp (mixedDiscriminantScale_pos K),
    positiveReal_cpow_eq_exp Real.pi_pos, ← Complex.exp_nat_mul, ← Complex.exp_add,
    quadraticHeckeFieldScale, Real.log_div (mixedDiscriminantScale_pos K).ne'
      (pow_ne_zero _ Real.pi_ne_zero), Real.log_pow]
  push_cast
  congr 1
  ring

variable [IsTotallyComplex K]

theorem mixedGammaFactor_totallyComplex_pow (s : ℂ) :
    mixedGammaFactor K s = mixedGammaAtom s ^ r := by
  unfold mixedGammaFactor
  have h (w : InfinitePlace K) : (InfinitePlace.mult w : ℂ) * s / 2 = s := by
    rw [(IsTotallyComplex.isComplex w).mult_eq_two]
    push_cast
    ring
  simp only [h]
  change (∏ _ : InfinitePlace K, mixedGammaAtom s) = _
  rw [Finset.prod_const, Finset.card_univ, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

theorem quadraticHeckeDualGamma_eq_mixed (s : ℂ) :
    quadraticHeckeDualGamma (quadraticHeckeFieldScale K) r s =
      (mixedDiscriminantScale K : ℂ) ^ (2 * s - 1) *
        mixedGammaFactor K s * mixedInverseGammaFactor K (1 - s) := by
  rw [quadraticHeckeDualGamma, quadraticHeckeFieldScale_exp K, mul_assoc,
    ← mul_pow, ← quadraticHeckeGammaAtom_ratio s, mul_pow, inv_pow, mixedInverseGammaFactor,
    mixedGammaFactor_totallyComplex_pow K, mixedGammaFactor_totallyComplex_pow K]
  ring

end
end ArtinMatthews
