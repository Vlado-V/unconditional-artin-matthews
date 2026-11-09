module

public import ArtinMatthews.ProbeIdealSourceRegions
public import ArtinMatthews.EisensteinAngularCyclotomic


set_option backward.privateInPublic true
@[expose] public section

/-! The actual all-prime good source correction with the global cubic angular
character. The quadratic global phase in the Poisson construction remains separate. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain AngularLambda
open scoped NumberField BigOperators Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {ζ : K}

omit [NumberField K] in
theorem probeIdealCharacter_minus_one_of_twelve (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (hχ : orderOf χ = 6) : χ (-1) = 1 := by
  let z : 𝓞 K := ⟨ζ, hζ.isIntegral (by decide)⟩
  have hz : z ^ 6 = -1 := by
    apply Subtype.ext
    change ζ ^ 6 = -1
    exact (hζ.pow_of_dvd (p := 6) (by decide) (by decide)).eq_neg_one_of_two_right
  let a : (𝓞 K) ⧸ P.asIdeal := Ideal.Quotient.mk P.asIdeal z
  have ha6 : a ^ 6 = -1 := by
    dsimp only [a]
    rw [← map_pow, hz, map_neg, map_one]
  have hau : IsUnit a := IsUnit.of_pow_eq_one (n := 12) (by
    rw [show 12 = 6 * 2 by decide, pow_mul, ha6, neg_one_sq]) (by decide)
  rw [← ha6, map_pow, ← χ.pow_apply' (by decide : 6 ≠ 0),
    (orderOf_dvd_iff_pow_eq_one).mp (by rw [hχ]), MulChar.one_apply hau]

omit [NumberField K] in
theorem probeIdealResidue_char_ne_two (P : HeightOneSpectrum (𝓞 K))
    (hsix : (6 : 𝓞 K) ∉ P.asIdeal) : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2 := by
  intro he
  have hz : (2 : (𝓞 K) ⧸ P.asIdeal) = 0 := by
    simpa only [he, Nat.cast_ofNat] using
      (CharP.cast_eq_zero ((𝓞 K) ⧸ P.asIdeal) (ringChar ((𝓞 K) ⧸ P.asIdeal)))
  have hm : (2 : 𝓞 K) ∈ P.asIdeal := Ideal.Quotient.eq_zero_iff_mem.mp (by
    simpa only [map_ofNat] using hz)
  apply hsix
  simpa only [show (3 : 𝓞 K) * 2 = 6 by norm_num] using P.asIdeal.mul_mem_left 3 hm

theorem probeIdealCyclotomicSource_regions (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (hsix : (6 : 𝓞 K) ∉ P.asIdeal)
    (η : ℂ) (hη : η ^ 6 = 1) (u : ((𝓞 K) ⧸ P.asIdeal)ˣ) (ξ w z : ℂ)
    (hregion : ArtinMatthews.probeEulerRegion ξ.re w.re z.re) :
    let χ := cyclotomicAngularResidueCharacter hζ P hsix
    let Q : ℝ := Ideal.absNorm P.asIdeal
    (1 - ArtinMatthews.probeLocalV Q z) * (1 - ArtinMatthews.probeLocalW Q (χ u) w) /
      (1 - ArtinMatthews.probeLocalD Q (η * (χ u)⁻¹) ξ) *
      probeIdealSourceSeries K P χ 0 (probeIdealGaussGamma K P χ 2)
        (probeIdealGaussLocalVartheta K P χ η) (χ u) ξ w z =
      ArtinMatthews.probeGoodPrimeCorrection Q (χ u) (η * (χ u)⁻¹)
        (star (cyclotomicAngularIdeal hζ P.asIdeal) ^ 6) ξ w z := by
  dsimp only
  have hχ := cyclotomicAngularResidueCharacter_order hζ P hsix
  have H := probeIdealGoodSourceSeries_regions K P
    (cyclotomicAngularResidueCharacter hζ P hsix) hχ
    (probeIdealCharacter_minus_one_of_twelve hζ P _ hχ)
    (probeIdealResidue_char_ne_two P hsix) η hη u ξ w z hregion
  rwa [cyclotomicAngularResidueCharacter_localLambda hζ P hsix] at H

theorem probeIdealCyclotomicSource_regions_bound (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (hsix : (6 : 𝓞 K) ∉ P.asIdeal)
    (η : ℂ) (hη : η ^ 6 = 1) (u : ((𝓞 K) ⧸ P.asIdeal)ˣ) (ξ w z : ℂ)
    (hregion : ArtinMatthews.probeEulerRegion ξ.re w.re z.re)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm P.asIdeal) :
    let χ := cyclotomicAngularResidueCharacter hζ P hsix
    let Q : ℝ := Ideal.absNorm P.asIdeal
    ‖(1 - ArtinMatthews.probeLocalV Q z) * (1 - ArtinMatthews.probeLocalW Q (χ u) w) /
      (1 - ArtinMatthews.probeLocalD Q (η * (χ u)⁻¹) ξ) *
      probeIdealSourceSeries K P χ 0 (probeIdealGaussGamma K P χ 2)
        (probeIdealGaussLocalVartheta K P χ η) (χ u) ξ w z - 1‖ ≤
      160 * Q ^ (-(1 + 1 / 4000 : ℝ)) := by
  have hχ := cyclotomicAngularResidueCharacter_order hζ P hsix
  exact probeIdealGoodSourceSeries_regions_bound K P
    (cyclotomicAngularResidueCharacter hζ P hsix) hχ
    (probeIdealCharacter_minus_one_of_twelve hζ P _ hχ)
    (probeIdealResidue_char_ne_two P hsix) η hη u ξ w z hregion hcut

end

end ArtinMatthews.VaryingKummerAnalytic
