module

public import ArtinMatthews.VaryingKummerAnalyticMixedRadialMellin


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit real/complex signature normalization for the mixed Gaussian Mellin factors. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedGammaFactor_signature (s : ℂ) :
    mixedGammaFactor K s =
      ((1/2 : ℂ)*(Real.pi : ℂ)^(-(s/2))*Complex.Gamma (s/2))^
          InfinitePlace.nrRealPlaces K *
      ((1/2 : ℂ)*(Real.pi : ℂ)^(-s)*Complex.Gamma s)^
          InfinitePlace.nrComplexPlaces K := by
  unfold mixedGammaFactor
  rw [InfinitePlace.prod_eq_prod_mul_prod]
  simp only [InfinitePlace.mult_isReal, InfinitePlace.mult_isComplex,
    Nat.cast_one, Nat.cast_ofNat, one_mul,
    show ∀ s : ℂ, 2*s/2 = s by intro s; ring,
    Finset.prod_const, Finset.card_univ]

theorem mixedRadialJacobian_signature :
    mixedRadialJacobian K = (2 / (Module.finrank ℚ K : ℝ)) *
      2^(InfinitePlace.nrComplexPlaces K) := by
  unfold mixedRadialJacobian
  rw [InfinitePlace.prod_eq_prod_mul_prod]
  simp only [InfinitePlace.mult_isReal, InfinitePlace.mult_isComplex,
    Nat.cast_one, Nat.cast_ofNat, Finset.prod_const_one, one_mul,
    Finset.prod_const, Finset.card_univ]

end
end ArtinMatthews.VaryingKummerAnalytic
