module

public import ArtinMatthews.ProbeEulerClassWeights
public import ArtinMatthews.ProbePrimeLocalCoefficient
public import ArtinMatthews.ProbeLocalEulerGeometric


set_option backward.privateInPublic true
@[expose] public section

/-! Exact summation of the actual surviving j=0 local classes.  This theorem
does not identify the constructed local correction with a global Hecke
character or claim the CRT factorization of the global probe. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField BigOperators Classical
noncomputable section

private theorem probe_tsum_indicator_mul (c : ℂ) (P : ℕ → ℕ → Prop)
    (f : ℕ → ℕ → ℂ) [∀ d r, Decidable (P d r)] :
    (∑' d : ℕ, ∑' r : ℕ, if P d r then c * f d r else 0) =
      c * ∑' d : ℕ, ∑' r : ℕ, if P d r then f d r else 0 := by
  have he (d r : ℕ) : (if P d r then c * f d r else 0) =
      c * (if P d r then f d r else 0) := by
    split_ifs <;> simp
  simp_rw [he, tsum_mul_left]

variable (K : Type*) [Field K] [NumberField K]

def probePrimeGroupedGoodSum (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (η θ a b V : ℂ) : ℂ :=
  let γ := probePrimeGaussGamma K p hp χ 2
  let v := probePrimeGaussLocalVartheta K p hp χ η
  (∑' r : ℕ, probePrimeLocalCoefficient K p hp χ 0 0 (6 * r) * V ^ r) +
    (∑' k : ℕ, (θ * b) ^ (k + 1) *
      ∑' r : ℕ, probePrimeLocalCoefficient K p hp χ 0 (k + 1) (6 * r) * V ^ r) +
    (∑' d : ℕ, ∑' r : ℕ, probeEulerZeroClassWeight K p hp χ v θ a b V 0 d r) +
    (∑' d : ℕ, ∑' r : ℕ, probeEulerZeroClassWeight K p hp χ v θ a b V 1 d r) +
    (∑' d : ℕ, ∑' r : ℕ, probeEulerOneClassWeight K p hp χ γ v θ a b V 0 d r) +
    (∑' d : ℕ, ∑' r : ℕ, probeEulerOneClassWeight K p hp χ γ v θ a b V 1 d r)

theorem probePrimeGroupedGoodSum_supported (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2)
    (η θ a b V : ℂ) (hθ : θ ^ 6 = 1) :
    probePrimeGroupedGoodSum K p hp.ne_zero χ η θ a b V =
      probeLocalSupportedEulerSeries (Ideal.absNorm (Ideal.span {p})) V (θ * b)
        (η * θ⁻¹ * a)
        ((probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
          (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6) := by
  let γ := probePrimeGaussGamma K p hp.ne_zero χ 2
  let v := probePrimeGaussLocalVartheta K p hp.ne_zero χ η
  let q : ℂ := Ideal.absNorm (Ideal.span {p})
  let R := v ^ 6 * q ^ 4 * a ^ 6
  let D := η * θ⁻¹ * a
  have hphase : γ * v * probePrimeTau K p hp.ne_zero χ *
      (Real.sqrt (Ideal.absNorm (Ideal.span {p})) : ℂ)⁻¹ = -η :=
    probePrimeEuler_phase_scalar K p hp χ hχ hchar η
  have h00 : (∑' r : ℕ, probePrimeLocalCoefficient K p hp.ne_zero χ 0 0 (6 * r) * V ^ r) =
      ∑' r : ℕ, V ^ r := by
    simp only [probePrimeLocalCoefficient_zero_zero, one_mul]
  have h01 : (∑' k : ℕ, (θ * b) ^ (k + 1) *
      ∑' r : ℕ, probePrimeLocalCoefficient K p hp.ne_zero χ 0 (k + 1) (6 * r) * V ^ r) =
      ∑' k : ℕ, (θ * b) ^ (k + 1) := by
    simp only [probePrimeLocalCoefficient_zero_succ K p hp, ite_mul, one_mul, zero_mul,
      tsum_ite_eq, pow_zero, mul_one]
  have h0 : (∑' d : ℕ, ∑' r : ℕ,
      probeEulerZeroClassWeight K p hp.ne_zero χ v θ a b V 0 d r) =
      (1 - q⁻¹) * ∑' d : ℕ, ∑' r : ℕ, if d < r then R ^ (d + 1) * V ^ r else 0 := by
    simp_rw [probeEulerZeroClassWeight_zero K p hp χ hχ v θ a b V hθ]
    calc
      _ = ∑' d : ℕ, ∑' r : ℕ, if d < r then (1 - q⁻¹) * (R ^ (d + 1) * V ^ r) else 0 := by
        apply tsum_congr
        intro d
        apply tsum_congr
        intro r
        split_ifs <;> dsimp [q, R]
        all_goals ring
      _ = _ := probe_tsum_indicator_mul (1 - q⁻¹) (fun d r => d < r)
        (fun d r => R ^ (d + 1) * V ^ r)
  have h1 : (∑' d : ℕ, ∑' r : ℕ,
      probeEulerZeroClassWeight K p hp.ne_zero χ v θ a b V 1 d r) =
      (θ * b) * ∑' d : ℕ, ∑' r : ℕ, if r = d + 1 then R ^ (d + 1) * V ^ r else 0 := by
    simp_rw [probeEulerZeroClassWeight_one K p hp χ hχ hminus v θ a b V hθ]
    calc
      _ = ∑' d : ℕ, ∑' r : ℕ, if r = d + 1 then (θ * b) * (R ^ (d + 1) * V ^ r) else 0 := by
        apply tsum_congr
        intro d
        apply tsum_congr
        intro r
        split_ifs <;> dsimp [R, q]
        all_goals ring
      _ = _ := probe_tsum_indicator_mul (θ * b) (fun d r => r = d + 1)
        (fun d r => R ^ (d + 1) * V ^ r)
  have h2 : (∑' d : ℕ, ∑' r : ℕ,
      probeEulerOneClassWeight K p hp.ne_zero χ γ v θ a b V 0 d r) =
      (-D) * ∑' d : ℕ, ∑' r : ℕ, if r = d then R ^ d * V ^ r else 0 := by
    simp_rw [probeEulerOneClassWeight_zero K p hp χ hχ γ v θ a b V η hθ hphase]
    simpa only [D, R, q, mul_assoc] using
      probe_tsum_indicator_mul (-D) (fun d r => r = d) (fun d r => R ^ d * V ^ r)
  have h3 : (∑' d : ℕ, ∑' r : ℕ,
      probeEulerOneClassWeight K p hp.ne_zero χ γ v θ a b V 1 d r) =
      (-(q - 1) * D * (θ * b)) *
        ∑' d : ℕ, ∑' r : ℕ, if d < r then R ^ d * V ^ r else 0 := by
    simp_rw [probeEulerOneClassWeight_one K p hp χ hχ hminus γ v θ a b V η hθ hphase]
    calc
      _ = ∑' d : ℕ, ∑' r : ℕ, if d < r then
          (-(q - 1) * D * (θ * b)) * (R ^ d * V ^ r) else 0 := by
        apply tsum_congr
        intro d
        apply tsum_congr
        intro r
        split_ifs <;> dsimp [D, R, q]
        all_goals ring
      _ = _ := probe_tsum_indicator_mul (-(q - 1) * D * (θ * b)) (fun d r => d < r)
        (fun d r => R ^ d * V ^ r)
  change _ = probeLocalSupportedEulerSeries q V (θ * b) D R
  unfold probePrimeGroupedGoodSum
  change _ + _ + _ + _ +
    (∑' d : ℕ, ∑' r : ℕ, probeEulerOneClassWeight K p hp.ne_zero χ γ v θ a b V 0 d r) +
    (∑' d : ℕ, ∑' r : ℕ, probeEulerOneClassWeight K p hp.ne_zero χ γ v θ a b V 1 d r) = _
  rw [h00, h01, h0, h1, h2, h3]
  unfold probeLocalSupportedEulerSeries
  ring

theorem probePrimeGroupedGoodSum_eq (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2)
    (η θ a b V : ℂ) (hθ : θ ^ 6 = 1) (hV : ‖V‖ < 1) (hW : ‖θ * b‖ < 1)
    (hE : ‖(probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6 * V‖ < 1) :
    probePrimeGroupedGoodSum K p hp.ne_zero χ η θ a b V =
      ArtinMatthews.probeGoodLocalFactor (Ideal.absNorm (Ideal.span {p})) V (θ * b)
        (η * θ⁻¹ * a)
        ((probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
          (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6 * V) := by
  rw [probePrimeGroupedGoodSum_supported K p hp χ hχ hminus hchar η θ a b V hθ]
  apply probeLocalSupportedEulerSeries_eq _ _ _ _ _ _ hV hW hE
  exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)

end

end ArtinMatthews.VaryingKummerAnalytic
