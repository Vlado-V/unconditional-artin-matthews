module

public import ArtinMatthews.ProbeBadPrimeSeries
public import ArtinMatthews.ProbeEulerPrimeNorms


set_option backward.privateInPublic true
@[expose] public section

/-! The actual bad-prime correction is 1+O(Q^(-1/4000)) on both
enlarged source regions. The coefficient estimates come from finite Gauss
sums; only the genuine local unit phases enter the analytic estimate. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical
noncomputable section

def probeBadFirstParameter (Q : ℝ) (γ ν θ ξ : ℂ) : ℂ :=
  γ * ν * θ⁻¹ * (Q : ℂ) ^ (-(1 / 2 + ξ))

def probeBadThetaParameter (Q : ℝ) (ν θ ξ : ℂ) : ℂ :=
  ν ^ 3 * (θ⁻¹) ^ 3 * (Q : ℂ) ^ (-(1 + 3 * ξ))

theorem probeBadFirstParameter_norm {Q : ℝ} (hQ : 0 < Q) (γ ν θ ξ : ℂ)
    (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1) :
    ‖probeBadFirstParameter Q γ ν θ ξ‖ = Q ^ (-(1 / 2 + ξ.re)) := by
  simp only [probeBadFirstParameter, norm_mul, norm_inv, hγ, hν, hθ, inv_one,
    one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  congr 1
  simp

theorem probeBadThetaParameter_norm {Q : ℝ} (hQ : 0 < Q) (ν θ ξ : ℂ)
    (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1) :
    ‖probeBadThetaParameter Q ν θ ξ‖ = Q ^ (-(1 + 3 * ξ.re)) := by
  simp only [probeBadThetaParameter, norm_mul, norm_inv, norm_pow, hν, hθ, inv_one,
    one_pow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  congr 1
  simp

theorem probeBadParameters_real (Q : ℝ) (hQ : 0 < Q) (γ ν θ ξ w z : ℂ)
    (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1) :
    probeBadE Q (probeBadFirstParameter Q γ ν θ ξ) = Q ^ (1 / 2 - ξ.re) ∧
    probeBadA Q (probeBadThetaParameter Q ν θ ξ) = Q ^ (2 - 3 * ξ.re) ∧
    probeBadT Q (ArtinMatthews.probeLocalW Q θ w) = Q ^ (1 / 2 - w.re) ∧
    ‖ArtinMatthews.probeLocalV Q z‖ = Q ^ (-(6 * z.re)) := by
  have hw : ‖ArtinMatthews.probeLocalW Q θ w‖ = Q ^ (-w.re) := by
    simp only [ArtinMatthews.probeLocalW, norm_mul, hθ, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  refine ⟨?_, ?_, ?_, ArtinMatthews.probeLocalV_norm Q hQ z⟩
  · rw [probeBadE, probeBadFirstParameter_norm hQ γ ν θ ξ hγ hν hθ]
    nth_rw 1 [← Real.rpow_one Q]
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  · rw [probeBadA, probeBadThetaParameter_norm hQ ν θ ξ hν hθ,
      ← Real.rpow_natCast Q 3, ← Real.rpow_add hQ]
    congr 1
    ring
  · rw [probeBadT, hw, Real.sqrt_eq_rpow, ← Real.rpow_add hQ]
    congr 1

theorem probeBadRegion_exponents {x w z : ℝ}
    (h : ArtinMatthews.probeEulerRegion x w z) :
    0 ≤ w ∧ 1 / 2 - x ≤ 0 ∧ 2 - 3 * x ≤ -(99 / 100) ∧
      1 - x - w ≤ -(1 / 4000) ∧ 299 / 100000 ≤ 6 * z := by
  rcases h with ⟨hx, hw, hz⟩ | ⟨hx, hw, hz⟩ <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

variable (K : Type*) [Field K] [NumberField K]

theorem probeBadParameters_small (Q : ℝ)
    (γ ν θ ξ w z : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Q)
    (hregion : ArtinMatthews.probeEulerRegion ξ.re w.re z.re) :
    probeBadA Q (probeBadThetaParameter Q ν θ ξ) ≤ 1 / 2 ∧
      ‖ArtinMatthews.probeLocalV Q z‖ ≤ 1 / 2 := by
  obtain ⟨hQ, hsmall, _⟩ := ArtinMatthews.probeEulerCutoff_spec hcut
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  obtain ⟨_, _, he, _, hz⟩ := probeBadRegion_exponents hregion
  obtain ⟨_, hA, _, hV⟩ := probeBadParameters_real Q hQ0 γ ν θ ξ w z hγ hν hθ
  rw [hA, hV]
  constructor
  · exact (Real.rpow_le_rpow_of_exponent_le hQ he).trans
      ((Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)).trans hsmall)
  · exact (Real.rpow_le_rpow_of_exponent_le hQ (by linarith)).trans hsmall

theorem probeBadPrimeCorrection_regions (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j)
    (γ ν θ ξ w z : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (hregion : ArtinMatthews.probeEulerRegion ξ.re w.re z.re) :
    ‖probeBadPrimeCorrection K p hp.ne_zero χ j
      (probeBadFirstParameter (Ideal.absNorm (Ideal.span {p})) γ ν θ ξ)
      (probeBadThetaParameter (Ideal.absNorm (Ideal.span {p})) ν θ ξ)
      (ArtinMatthews.probeLocalW (Ideal.absNorm (Ideal.span {p})) θ w)
      (ArtinMatthews.probeLocalV (Ideal.absNorm (Ideal.span {p})) z) - 1‖ ≤
        36 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(1 / 4000 : ℝ)) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  obtain ⟨hQ, hsmall, _⟩ := ArtinMatthews.probeEulerCutoff_spec hcut
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  obtain ⟨hw, hx, hAexp, hETexp, hz⟩ := probeBadRegion_exponents hregion
  obtain ⟨hE, hA, hT, hV⟩ := probeBadParameters_real Q hQ0 γ ν θ ξ w z hγ hν hθ
  have hAA : Q ^ (2 - 3 * ξ.re) ≤ Q ^ (-(99 / 100 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hQ hAexp
  have hAh : Q ^ (2 - 3 * ξ.re) ≤ 1 / 2 := hAA.trans
    ((Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)).trans hsmall)
  have hVh : Q ^ (-(6 * z.re)) ≤ 1 / 2 :=
    (Real.rpow_le_rpow_of_exponent_le hQ (by linarith)).trans hsmall
  have hEE : Q ^ (1 / 2 - ξ.re) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hQ hx
  have hTT : Q ^ (1 / 2 - w.re) ≤ Q ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  have hET : Q ^ (1 / 2 - ξ.re) * Q ^ (1 / 2 - w.re) ≤ Q ^ (-(1 / 4000 : ℝ)) := by
    rw [← Real.rpow_add hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ
    linarith
  have hhalf : 1 ≤ Q ^ (1 / 2 : ℝ) := Real.one_le_rpow hQ (by norm_num)
  have hprod : (1 + Q ^ (1 / 2 - ξ.re)) * (1 + Q ^ (1 / 2 - w.re)) *
      Q ^ (2 - 3 * ξ.re) ≤ 4 * Q ^ (-(49 / 100 : ℝ)) := by
    calc
      _ ≤ (1 + 1) * (2 * Q ^ (1 / 2 : ℝ)) * Q ^ (-(99 / 100 : ℝ)) := by
        gcongr
        linarith
      _ = _ := by
        rw [mul_assoc, mul_assoc, ← Real.rpow_add hQ0]
        norm_num
        ring
  have hlast : Q ^ (-(49 / 100 : ℝ)) ≤ Q ^ (-(1 / 4000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)
  have H := probeBadPrimeCorrection_norm_sub_one_le K p hp χ hχ hminus j hj
    (probeBadFirstParameter Q γ ν θ ξ) (probeBadThetaParameter Q ν θ ξ)
    (ArtinMatthews.probeLocalW Q θ w) (ArtinMatthews.probeLocalV Q z)
    (by rwa [hA]) (by rwa [hV])
  rw [hE, hA, hT] at H
  change _ ≤ 36 * Q ^ (-(1 / 4000 : ℝ))
  nlinarith

theorem probeBadPrimeCorrection_actual_regions (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2)
    (η : ℂ) (hη : ‖η‖ = 1) (u : 𝓞 K) (hu : ¬p ∣ u) (j : ℕ) (hj : 0 < j)
    (ξ w z : ℂ)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (hregion : ArtinMatthews.probeEulerRegion ξ.re w.re z.re) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let γ := probePrimeGaussGamma K p hp.ne_zero χ 2
    let ν := probePrimeGaussLocalVartheta K p hp.ne_zero χ η
    let θ := χ (Ideal.Quotient.mk _ u)
    ‖probeBadPrimeCorrection K p hp.ne_zero χ j
      (probeBadFirstParameter Q γ ν θ ξ) (probeBadThetaParameter Q ν θ ξ)
      (ArtinMatthews.probeLocalW Q θ w) (ArtinMatthews.probeLocalV Q z) - 1‖ ≤
        36 * Q ^ (-(1 / 4000 : ℝ)) := by
  apply probeBadPrimeCorrection_regions K p hp χ hχ hminus j hj
  · exact probePrimeGaussGamma_norm_one K p hp χ hχ 2 (by decide) (by decide)
  · rw [probePrimeGaussLocalVartheta_norm K p hp χ hχ hchar, hη]
  · exact probePrimeCharacter_unit_norm K p hp χ hχ u hu
  · exact hcut
  · exact hregion

end
end ArtinMatthews.VaryingKummerAnalytic
