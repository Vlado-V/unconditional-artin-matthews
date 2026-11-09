module

public import ArtinMatthews.SourceThetaPhaseComparison
public import ArtinMatthews.ProbeBadIdealRegions


set_option backward.privateInPublic true
@[expose] public section

/-! The literal masked exterior coefficients for the three extracted
Euler factors. At a prime dividing u, both the numerator character
and its reciprocal-L twist have value zero. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open SIntegerQuotient SIntegerFourier SourceCRTNormalization AngularLambda
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (u : sourceRing F S₀) (hu : u ≠ 0)

theorem sourceResidualCharacter_pow_six (P : SourceExteriorPrime F S₀) :
    (sourceResidualCharacterUnit F hζ S₀ u hu P : ℂ) ^ 6 = 1 := by
  have h : sourceResidualCharacterUnit F hζ S₀ u hu P ^ (6 : ℕ) = 1 :=
    sourcePrimeCharacterUnit_pow_six F hζ S₀ P _ _
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
    congrArg (fun z : ℂˣ => (z : ℂ)) h

theorem sourceResidualCharacter_norm_one (P : SourceExteriorPrime F S₀) :
    ‖(sourceResidualCharacterUnit F hζ S₀ u hu P : ℂ)‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (6 : ℕ) ≠ 0)).mp
  rw [← norm_pow, sourceResidualCharacter_pow_six F hζ S₀ u hu P, norm_one]

theorem sourceResidualCharacter_inv (P : SourceExteriorPrime F S₀) :
    (sourceResidualCharacterUnit F hζ S₀ u hu P : ℂ)⁻¹ =
      star (sourceResidualCharacterUnit F hζ S₀ u hu P : ℂ) :=
  Complex.inv_eq_conj (sourceResidualCharacter_norm_one F hζ S₀ u hu P)

def sourcePrimeRowCharacter (P : SourceExteriorPrime F S₀) : ℂ :=
  if sourceElementExponents F S₀ u hu P = 0 then
    (sourceResidualCharacterUnit F hζ S₀ u hu P : ℂ) else 0

theorem sourcePrimeRowCharacter_of_degree_zero (P : SourceExteriorPrime F S₀)
    (hP : sourceElementExponents F S₀ u hu P = 0) :
    sourcePrimeRowCharacter F hζ S₀ u hu P = (sourceResidualCharacterUnit F hζ S₀ u hu P : ℂ) :=
  ite_eq_left hP

theorem sourcePrimeRowCharacter_of_degree_pos (P : SourceExteriorPrime F S₀)
    (hP : 0 < sourceElementExponents F S₀ u hu P) :
    sourcePrimeRowCharacter F hζ S₀ u hu P = 0 :=
  ite_eq_right (Nat.ne_of_gt hP)

theorem sourcePrimeRowCharacter_eq_residue (P : SourceExteriorPrime F S₀)
    (hP : sourceElementExponents F S₀ u hu P = 0) :
    sourcePrimeRowCharacter F hζ S₀ u hu P =
      generatorResidueCharacter (sourceHilbertSeed F S₀) P.val P.property
        (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
        (reflectionPrimeCharacters F hζ S₀ P) (Ideal.Quotient.mk _ u) := by
  let a := sourceAllowedPrimeGenerator F hζ S₀ P
  let ha := sourceAllowedPrimeGenerator_ideal F hζ S₀ P
  let χ := reflectionPrimeCharacters F hζ S₀ P
  let x := sourceFrequencyCofactor F S₀ hζ u hu 0 P
  have he := sourceFrequencyCofactor_base F hζ S₀ u hu P
  rw [hP, pow_zero, one_mul] at he
  calc
    _ = (sourceResidualCharacterUnit F hζ S₀ u hu P : ℂ) :=
      sourcePrimeRowCharacter_of_degree_zero F hζ S₀ u hu P hP
    _ = generatorResidueCharacter (sourceHilbertSeed F S₀) P.val P.property a ha χ (Ideal.Quotient.mk _ x) :=
      sourceCharacterUnit_val (sourceHilbertSeed F S₀) P.val P.property a ha χ x
        (sourceFrequencyCofactor_spec F S₀ hζ u hu 0 P).2
    _ = _ := congrArg (fun y : sourceRing F S₀ => generatorResidueCharacter
      (sourceHilbertSeed F S₀) P.val P.property a ha χ (Ideal.Quotient.mk _ y)) he.symm

theorem sourcePrimeRowCharacter_norm_le_one (P : SourceExteriorPrime F S₀) :
    ‖sourcePrimeRowCharacter F hζ S₀ u hu P‖ ≤ 1 := by
  unfold sourcePrimeRowCharacter
  split_ifs with h
  · rw [sourceResidualCharacter_norm_one F hζ S₀ u hu P]
  · simp

theorem sourcePrimeRowCharacter_one (P : SourceExteriorPrime F S₀) :
    sourcePrimeRowCharacter F hζ S₀ 1 one_ne_zero P = 1 := by
  rw [sourcePrimeRowCharacter_of_degree_zero F hζ S₀ 1 one_ne_zero P
      (by rw [sourceElementExponents_one, Finsupp.zero_apply]),
    sourceResidualCharacterUnit_one, Units.val_one]

variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)

def sourcePrimeRowTwist (P : SourceExteriorPrime F S₀) : ℂ :=
  η.allCoefficient P.val.asIdeal * star (sourcePrimeRowCharacter F hζ S₀ u hu P)

def sourcePrimeRowThirdPhase (P : SourceExteriorPrime F S₀) : ℂ :=
  if sourceElementExponents F S₀ u hu P = 0 then principalAngularThirdPhase hζ η P.val else 0

theorem sourcePrimeRowTwist_norm_le_one (P : SourceExteriorPrime F S₀) :
    ‖sourcePrimeRowTwist F hζ S₀ u hu η P‖ ≤ 1 := by
  rw [sourcePrimeRowTwist, norm_mul, norm_star]
  calc
    _ ≤ 1 * ‖sourcePrimeRowCharacter F hζ S₀ u hu P‖ :=
      mul_le_mul_of_nonneg_right (η.allCoefficient_norm_le_one P.val.asIdeal) (norm_nonneg _)
    _ ≤ 1 := by
      rw [one_mul]
      exact sourcePrimeRowCharacter_norm_le_one F hζ S₀ u hu P

theorem sourcePrimeRowThirdPhase_norm_le_one (P : SourceExteriorPrime F S₀) :
    ‖sourcePrimeRowThirdPhase F hζ S₀ u hu η P‖ ≤ 1 := by
  unfold sourcePrimeRowThirdPhase
  split_ifs
  · exact principalAngularThirdPhase_norm_le_one hζ η P.val
  · simp

theorem sourcePrimeOldTheta_sixth (P : SourceExteriorPrime F S₀) :
    probeIdealGaussLocalVartheta F P.val (reflectionPrimeCharacters F hζ S₀ P)
        (η.allCoefficient P.val.asIdeal) ^ 6 = principalAngularThirdPhase hζ η P.val := by
  let χ := reflectionPrimeCharacters F hζ S₀ P
  have hsix := source_exterior_six_not_mem F S₀ P.val P.property
  have hLambda : probeIdealGaussLocalLambda F P.val χ = cyclotomicAngularIdeal hζ P.val.asIdeal :=
    cyclotomicAngularResidueCharacter_localLambda hζ P.val hsix
  rw [probeIdealGauss_vartheta_sixth F P.val χ (sourcePrimeCharacter_order F hζ S₀ P)
    (sourcePrimeCharacter_minus_one F hζ S₀ P) (sourcePrimeResidue_char_ne_two F S₀ P), hLambda]
  rfl

theorem sourceInitialCoordinates_region (ξ w z : ℂ) (hξ : 2 < ξ.re)
    (hw : 2 < w.re) (hz : 1 / 6 < z.re) : (ξ, w, z) ∈ probeEulerDomain :=
  Or.inr ⟨by dsimp; linarith, by dsimp; linarith, by dsimp; linarith⟩

theorem sourceLocalParameters_norm_lt_one (P : ProbePrime F) (a b c : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (ξ w z : ℂ) (hq : (ξ, w, z) ∈ probeEulerDomain) :
    let Q : ℝ := Ideal.absNorm P.asIdeal
    ‖probeLocalV Q z‖ < 1 ∧ ‖probeLocalW Q a w‖ < 1 ∧
      ‖probeLocalD Q b ξ‖ < 1 ∧ ‖probeLocalE Q c ξ z‖ < 1 := by
  let Q : ℝ := Ideal.absNorm P.asIdeal
  have hQ : 1 < Q := probeIdealPrime_norm_gt_one F P
  have hQ0 : 0 < Q := lt_trans zero_lt_one hQ
  obtain ⟨hx, hw, hz, he⟩ := probeEulerRegion_individual hq
  change ‖probeLocalV Q z‖ < 1 ∧ ‖probeLocalW Q a w‖ < 1 ∧
      ‖probeLocalD Q b ξ‖ < 1 ∧ ‖probeLocalE Q c ξ z‖ < 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [probeLocalV_norm Q hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  · exact (probeLocalW_norm_le Q hQ0 a w ha).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith))
  · exact (probeLocalD_norm_le Q hQ0 b ξ hb).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith))
  · exact (probeLocalE_norm_le Q hQ0 c ξ z hc).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith))

end
end ArtinMatthews.SourceEulerAssembly
