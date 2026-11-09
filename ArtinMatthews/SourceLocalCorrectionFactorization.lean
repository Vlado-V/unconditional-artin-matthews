module

public import ArtinMatthews.SourceLocalFactorPhaseInvariant
public import ArtinMatthews.SourceAnalyticEulerParameters


set_option backward.privateInPublic true
@[expose] public section

/-! Exact local extraction of the zeta numerator, the masked row L
numerator and the reciprocal twist L from the literal source factor. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)
variable (u : sourceRing F S₀) (hu : u ≠ 0)
variable (P : SourceExteriorPrime F S₀)

local notation "χ" => reflectionPrimeCharacters F hζ S₀ P
local notation "θ" => (sourceResidualCharacterUnit F hζ S₀ u hu P : ℂ)
local notation "ν" => probeIdealGaussLocalVartheta F P.val χ (η.allCoefficient P.val.asIdeal)
local notation "γ" => probeIdealGaussGamma F P.val χ 2
local notation "j" => sourceElementExponents F S₀ u hu P
local notation "Q" => (Ideal.absNorm P.val.asIdeal : ℝ)
local notation "a" => sourcePrimeRowCharacter F hζ S₀ u hu P
local notation "b" => sourcePrimeRowTwist F hζ S₀ u hu η P
local notation "c" => sourcePrimeRowThirdPhase F hζ S₀ u hu η P

omit [IsTotallyComplex F] in
def sourcePrimeBadCorrection : ProbeCoordinates → ℂ :=
  probeBadIdealSourceCorrection F P.val χ j γ ν θ

omit [IsTotallyComplex F] in
def sourcePrimeRowCorrection (q : ProbeCoordinates) : ℂ :=
  if j = 0 then probeGoodPrimeCorrection Q a b c q.1 q.2.1 q.2.2
  else sourcePrimeBadCorrection F hζ S₀ η u hu P q

theorem sourceGoodLocalFactor_eq_rational (hj : j = 0) (ξ w z : ℂ)
    (hξ : 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    sourceLocalEulerFactor F hζ S₀ hS η u hu ξ w z P =
      probeGoodLocalFactor (Q : ℂ) (probeLocalV Q z) (probeLocalW Q a w)
        (probeLocalD Q b ξ) (probeLocalE Q c ξ z) := by
  have ha : a = θ := sourcePrimeRowCharacter_of_degree_zero F hζ S₀ u hu P hj
  have hb : b = η.allCoefficient P.val.asIdeal * θ⁻¹ := by
    rw [sourcePrimeRowTwist, ha, sourceResidualCharacter_inv F hζ S₀ u hu P]
  have hc : c = ν ^ 6 := by
    unfold sourcePrimeRowThirdPhase
    rw [ite_eq_left hj, sourcePrimeOldTheta_sixth F hζ S₀ η P]
  obtain ⟨hV, hW, _, hE⟩ := sourceLocalParameters_norm_lt_one F P.val a b c
    (sourcePrimeRowCharacter_norm_le_one F hζ S₀ u hu P)
    (sourcePrimeRowTwist_norm_le_one F hζ S₀ u hu η P)
    (sourcePrimeRowThirdPhase_norm_le_one F hζ S₀ u hu η P)
    ξ w z (sourceInitialCoordinates_region ξ w z hξ hw hz)
  rw [ha] at hW
  rw [hc] at hE
  rw [sourceLocalEulerFactor_eq_ideal F hζ S₀ hS η u hu ξ w z P hξ hw hz,
    hj, ha, hb, hc]
  exact probeIdealGoodSourceSeries_eq_factor F P.val χ
    (sourcePrimeCharacter_order F hζ S₀ P) (sourcePrimeCharacter_minus_one F hζ S₀ P)
    (sourcePrimeResidue_char_ne_two F S₀ P) (η.allCoefficient P.val.asIdeal) θ ξ w z
    (sourceResidualCharacter_pow_six F hζ S₀ u hu P) hV hW hE

theorem sourceOneSub_ne_zero_of_norm_lt_one {b₀ : ℂ} (h : ‖b₀‖ < 1) : 1 - b₀ ≠ 0 := by
  intro he
  rw [← sub_eq_zero.mp he, norm_one] at h
  exact lt_irrefl _ h

theorem sourceLocalEulerFactor_normalized (ξ w z : ℂ)
    (hξ : 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    sourceLocalEulerFactor F hζ S₀ hS η u hu ξ w z P =
      (1 - probeLocalV Q z)⁻¹ * (1 - probeLocalW Q a w)⁻¹ * (1 - probeLocalD Q b ξ) *
        sourcePrimeRowCorrection F hζ S₀ η u hu P (ξ, w, z) := by
  obtain ⟨hV, hW, hD, _⟩ := sourceLocalParameters_norm_lt_one F P.val a b c
    (sourcePrimeRowCharacter_norm_le_one F hζ S₀ u hu P)
    (sourcePrimeRowTwist_norm_le_one F hζ S₀ u hu η P)
    (sourcePrimeRowThirdPhase_norm_le_one F hζ S₀ u hu η P)
    ξ w z (sourceInitialCoordinates_region ξ w z hξ hw hz)
  have hV0 := sourceOneSub_ne_zero_of_norm_lt_one hV
  have hW0 := sourceOneSub_ne_zero_of_norm_lt_one hW
  have hD0 := sourceOneSub_ne_zero_of_norm_lt_one hD
  by_cases hj : j = 0
  · rw [sourceGoodLocalFactor_eq_rational F hζ S₀ hS η u hu P hj ξ w z hξ hw hz,
      sourcePrimeRowCorrection, ite_eq_left hj]
    unfold probeGoodPrimeCorrection probeGoodLocalCorrection
    dsimp only
    field_simp
  · have ha0 : a = 0 := ite_eq_right hj
    have hb0 : b = 0 := by rw [sourcePrimeRowTwist, ha0, star_zero, mul_zero]
    rw [sourceLocalEulerFactor_eq_ideal F hζ S₀ hS η u hu ξ w z P hξ hw hz,
      sourcePrimeRowCorrection, ite_eq_right hj, ha0, hb0]
    unfold sourcePrimeBadCorrection probeBadIdealSourceCorrection
    simp only [probeLocalW, probeLocalD, zero_mul, sub_zero, inv_one, mul_one]
    rw [← mul_assoc, inv_mul_cancel₀ hV0, one_mul]

end
end ArtinMatthews.SourceEulerAssembly
