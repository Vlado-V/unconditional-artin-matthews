module

public import ArtinMatthews.ProbePrimeRawAnalyticFactor
public import ArtinMatthews.ProbeIdealRawEuler
public import ArtinMatthews.ProbeIdealPhasePowers
public import ArtinMatthews.ProbeEulerRegions


set_option backward.privateInPublic true
@[expose] public section

/-! Complex-power specialization of the literal j=0 local series to the
named rational factor used by the analytic Euler-product construction. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeIdealRawLocal_analytic_factor (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η θ x w z : ℂ) (hθ : θ ^ 6 = 1) :
    let Q : ℝ := Ideal.absNorm (P.asIdeal)
    let v := probeIdealGaussLocalVartheta K P χ η
    ‖ArtinMatthews.probeLocalV Q z‖ < 1 →
    ‖ArtinMatthews.probeLocalW Q θ w‖ < 1 →
    ‖ArtinMatthews.probeLocalE Q (v ^ 6) x z‖ < 1 →
    probeIdealRawLocalSeries K P χ η θ ((Q : ℂ) ^ (-x))
      ((Q : ℂ) ^ (-w)) (ArtinMatthews.probeLocalV Q z) =
      ArtinMatthews.probeGoodLocalFactor (Q : ℂ)
        (ArtinMatthews.probeLocalV Q z) (ArtinMatthews.probeLocalW Q θ w)
        (ArtinMatthews.probeLocalD Q (η * θ⁻¹) x)
        (ArtinMatthews.probeLocalE Q (v ^ 6) x z) := by
  dsimp only
  intro hV hW hE
  have hq : (Ideal.absNorm (P.asIdeal) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      P.ne_bot
  have he : (probeIdealGaussLocalVartheta K P χ η) ^ 6 *
      (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 *
      ((Ideal.absNorm (P.asIdeal) : ℂ) ^ (-x)) ^ 6 *
      ArtinMatthews.probeLocalV (Ideal.absNorm (P.asIdeal)) z =
      ArtinMatthews.probeLocalE (Ideal.absNorm (P.asIdeal))
        ((probeIdealGaussLocalVartheta K P χ η) ^ 6) x z := by
    simp only [ArtinMatthews.probeLocalV, ArtinMatthews.probeLocalE, Complex.ofReal_natCast]
    rw [mul_assoc, mul_assoc]
    congr 1
    simpa only [mul_assoc] using probe_cpow_local_geometric _ hq x z
  have h := probeIdealRawLocalSeries_eq K P χ hχ hminus hchar η θ
    ((Ideal.absNorm (P.asIdeal) : ℂ) ^ (-x))
    ((Ideal.absNorm (P.asIdeal) : ℂ) ^ (-w))
    (ArtinMatthews.probeLocalV (Ideal.absNorm (P.asIdeal)) z) hθ hV hW (he.symm ▸ hE)
  rw [he] at h
  simpa only [ArtinMatthews.probeLocalW, ArtinMatthews.probeLocalD,
    Complex.ofReal_natCast, mul_assoc] using h

theorem probeIdealRawLocal_analytic_correction (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η θ x w z : ℂ) (hθ : θ ^ 6 = 1) :
    let Q : ℝ := Ideal.absNorm (P.asIdeal)
    let v := probeIdealGaussLocalVartheta K P χ η
    ‖ArtinMatthews.probeLocalV Q z‖ < 1 →
    ‖ArtinMatthews.probeLocalW Q θ w‖ < 1 →
    ‖ArtinMatthews.probeLocalE Q (v ^ 6) x z‖ < 1 →
    (1 - ArtinMatthews.probeLocalV Q z) * (1 - ArtinMatthews.probeLocalW Q θ w) /
      (1 - ArtinMatthews.probeLocalD Q (η * θ⁻¹) x) *
      probeIdealRawLocalSeries K P χ η θ ((Q : ℂ) ^ (-x))
        ((Q : ℂ) ^ (-w)) (ArtinMatthews.probeLocalV Q z) =
      ArtinMatthews.probeGoodPrimeCorrection Q θ (η * θ⁻¹) (v ^ 6) x w z := by
  dsimp only
  intro hV hW hE
  rw [probeIdealRawLocal_analytic_factor K P χ hχ hminus hchar η θ x w z hθ hV hW hE]
  rfl


theorem probeIdealRawLocal_cubic_correction (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η θ x w z : ℂ) (hη : η ^ 6 = 1) (hθ : θ ^ 6 = 1) :
    let Q : ℝ := Ideal.absNorm P.asIdeal
    let Λ := star (probeIdealGaussLocalLambda K P χ) ^ 6
    ‖ArtinMatthews.probeLocalV Q z‖ < 1 →
    ‖ArtinMatthews.probeLocalW Q θ w‖ < 1 →
    ‖ArtinMatthews.probeLocalE Q Λ x z‖ < 1 →
    (1 - ArtinMatthews.probeLocalV Q z) * (1 - ArtinMatthews.probeLocalW Q θ w) /
      (1 - ArtinMatthews.probeLocalD Q (η * θ⁻¹) x) *
      probeIdealRawLocalSeries K P χ η θ ((Q : ℂ) ^ (-x))
        ((Q : ℂ) ^ (-w)) (ArtinMatthews.probeLocalV Q z) =
      ArtinMatthews.probeGoodPrimeCorrection Q θ (η * θ⁻¹) Λ x w z := by
  dsimp only
  rw [← probeIdealGauss_vartheta_sixth_of_eta K P χ hχ hminus hchar η hη]
  exact probeIdealRawLocal_analytic_correction K P χ hχ hminus hchar η θ x w z hθ

end

end ArtinMatthews.VaryingKummerAnalytic
