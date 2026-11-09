module

public import ArtinMatthews.ProbeBadPrimeSourceWeight
public import ArtinMatthews.ProbeBadPrimeProductBound


set_option backward.privateInPublic true
@[expose] public section

/-! Actual bad-prime local data, including the genuine finite Gauss
phases, and the subpower bound on any subset of an ideal's prime support.
The omitted global CRT/Hecke-phase identification is not an input. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical BigOperators
noncomputable section

structure ProbeBadPrimeData (K : Type*) [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) where
  prime : 𝓞 K
  prime_isPrime : Prime prime
  span_eq : Ideal.span {prime} = P
  character : MulChar ((𝓞 K) ⧸ Ideal.span {prime}) ℂ
  order_six : orderOf character = 6
  minus_one : character (-1) = 1
  residue_char_ne_two : ringChar ((𝓞 K) ⧸ Ideal.span {prime}) ≠ 2
  eta : ℂ
  eta_norm : ‖eta‖ = 1
  unit : 𝓞 K
  prime_not_dvd_unit : ¬prime ∣ unit
  valuation : ℕ
  valuation_pos : 0 < valuation
  valuation_lt_six : valuation < 6
  norm_large : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm P

namespace ProbeBadPrimeData
variable {K : Type*} [Field K] [NumberField K] {P : Ideal (𝓞 K)}
variable (D : ProbeBadPrimeData K P)

def gamma : ℂ := probePrimeGaussGamma K D.prime D.prime_isPrime.ne_zero D.character 2
def vartheta : ℂ := probePrimeGaussLocalVartheta K D.prime D.prime_isPrime.ne_zero D.character D.eta
def theta : ℂ := D.character (Ideal.Quotient.mk _ D.unit)

theorem phase_norms : ‖D.gamma‖ = 1 ∧ ‖D.vartheta‖ = 1 ∧ ‖D.theta‖ = 1 := by
  refine ⟨probePrimeGaussGamma_norm_one K D.prime D.prime_isPrime D.character D.order_six
    2 (by decide) (by decide), ?_, ?_⟩
  · rw [vartheta, probePrimeGaussLocalVartheta_norm K D.prime D.prime_isPrime D.character
      D.order_six D.residue_char_ne_two, D.eta_norm]
  · exact probePrimeCharacter_unit_norm K D.prime D.prime_isPrime D.character D.order_six
      D.unit D.prime_not_dvd_unit

def correction (ξ w z : ℂ) : ℂ :=
  let Q : ℝ := Ideal.absNorm (Ideal.span {D.prime})
  (1 - ArtinMatthews.probeLocalV Q z) *
    probeBadPrimeSourceSeries K D.prime D.prime_isPrime.ne_zero D.character D.valuation
      D.gamma D.vartheta D.theta ξ w z

theorem correction_norm_sub_one_le (ξ w z : ℂ)
    (hregion : ArtinMatthews.probeEulerRegion ξ.re w.re z.re) :
    ‖D.correction ξ w z - 1‖ ≤ 36 * (Ideal.absNorm P : ℝ) ^ (-(1 / 4000 : ℝ)) := by
  have hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm (Ideal.span {D.prime}) := by
    rw [D.span_eq]
    exact D.norm_large
  obtain ⟨hγ, hν, hθ⟩ := D.phase_norms
  have H := probeBadPrimeSourceCorrection_regions K D.prime D.prime_isPrime D.character D.order_six
    D.minus_one D.valuation D.valuation_pos D.gamma D.vartheta D.theta ξ w z hγ hν hθ hcut hregion
  simpa only [correction, D.span_eq] using H

theorem correction_norm_le (ξ w z : ℂ)
    (hregion : ArtinMatthews.probeEulerRegion ξ.re w.re z.re) : ‖D.correction ξ w z‖ ≤ 64 := by
  have hQ : 1 ≤ (Ideal.absNorm P : ℝ) := by
    rw [← D.span_eq]
    exact probePrimeNorm_one_le K D.prime D.prime_isPrime.ne_zero
  have hp : (Ideal.absNorm P : ℝ) ^ (-(1 / 4000 : ℝ)) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hQ (by norm_num : -(1 / 4000 : ℝ) ≤ 0)
  have H := D.correction_norm_sub_one_le ξ w z hregion
  have ht := norm_add_le (D.correction ξ w z - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at ht
  linarith

end ProbeBadPrimeData

theorem exists_actual_badPrime_product_subpower_bound
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)), I ≠ ⊥ →
      ∀ (T : Finset (Ideal (𝓞 K))), T ⊆ HeckeIdealMobius.primeSupport K I →
      ∀ (D : ∀ P : T, ProbeBadPrimeData K P.val) (ξ w z : ℂ),
      ArtinMatthews.probeEulerRegion ξ.re w.re z.re →
      ‖∏ P : T, (D P).correction ξ w z‖ ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := exists_probe_primeSubset_product_bound K ε hε
  exact ⟨C, hC, fun I hI T hT D ξ w z hregion =>
    h I hI T hT (fun P => (D P).correction ξ w z)
      (fun P => (D P).correction_norm_le ξ w z hregion)⟩

theorem exists_actual_badPrime_product_fixed_support_bound
    (K : Type*) [Field K] [NumberField K] (R : Ideal (𝓞 K)) (hR : R ≠ ⊥)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Ideal (𝓞 K)), U ≠ ⊥ →
      ∀ (T : Finset (Ideal (𝓞 K))), T ⊆ HeckeIdealMobius.primeSupport K (U * R) →
      ∀ (D : ∀ P : T, ProbeBadPrimeData K P.val) (ξ w z : ℂ),
      ArtinMatthews.probeEulerRegion ξ.re w.re z.re →
      ‖∏ P : T, (D P).correction ξ w z‖ ≤ C * (Ideal.absNorm U : ℝ) ^ ε := by
  obtain ⟨B, hB, h⟩ := exists_actual_badPrime_product_subpower_bound K ε hε
  have hRN : 0 < (Ideal.absNorm R : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hR)
  refine ⟨B * (Ideal.absNorm R : ℝ) ^ ε, mul_pos hB (Real.rpow_pos_of_pos hRN _), ?_⟩
  intro U hU T hT D ξ w z hregion
  have hUR : U * R ≠ ⊥ := mul_ne_zero hU hR
  have H := h (U * R) hUR T hT D ξ w z hregion
  rw [map_mul, Nat.cast_mul, Real.mul_rpow (by positivity) hRN.le] at H
  exact H.trans_eq (by ring)

end
end ArtinMatthews.VaryingKummerAnalytic
