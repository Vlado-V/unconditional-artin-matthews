module

public import ArtinMatthews.ProbeBadPrimeRegions
public import ArtinMatthews.ProbeBadPrimeOriginal


set_option backward.privateInPublic true
@[expose] public section

/-! Identification of the grouped weights with the literal source-05
e0,l,k,m summand, including its complex power of the prime norm. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def probeBadPrimeSourceTerm (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (j : ℕ)
    (γ ν θ ξ w z : ℂ) (e : Fin 2) (l k m : ℕ) : ℂ :=
  probePrimeLocalCoefficient K p hp χ (e.val + 3 * l) k (j + 6 * m) *
    γ ^ e.val * ν ^ (e.val + 3 * l) * θ ^ k * (θ⁻¹) ^ (e.val + 3 * l) *
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^
        (-((e.val : ℂ) * (1 / 2 + ξ) + (l : ℂ) * (1 + 3 * ξ) + (k : ℂ) * w + (6 * m : ℂ) * z))

theorem probeBadPrimeWeight_eq_source (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (j : ℕ)
    (γ ν θ ξ w z : ℂ) (e : Fin 2) (l k m : ℕ) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    probeBadPrimeWeight K p hp χ j (probeBadFirstParameter Q γ ν θ ξ)
      (probeBadThetaParameter Q ν θ ξ) (ArtinMatthews.probeLocalW Q θ w)
      (ArtinMatthews.probeLocalV Q z) e l k m =
      probeBadPrimeSourceTerm K p hp χ j γ ν θ ξ w z e l k m := by
  let Q : ℂ := Ideal.absNorm (Ideal.span {p})
  have hQ : Q ≠ 0 := by
    dsimp only [Q]
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp)
  have hpow : (Q ^ (-(1 / 2 + ξ))) ^ e.val * (Q ^ (-(1 + 3 * ξ))) ^ l *
      (Q ^ (-w)) ^ k * (Q ^ (-(6 * z))) ^ m =
      Q ^ (-((e.val : ℂ) * (1 / 2 + ξ) + (l : ℂ) * (1 + 3 * ξ) + (k : ℂ) * w + (6 * m : ℂ) * z)) := by
    rw [← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
      ← Complex.cpow_add _ _ hQ, ← Complex.cpow_add _ _ hQ, ← Complex.cpow_add _ _ hQ]
    congr 1
    ring
  dsimp only
  unfold probeBadPrimeWeight probeBadFirstParameter probeBadThetaParameter
    ArtinMatthews.probeLocalW ArtinMatthews.probeLocalV probeBadPrimeSourceTerm
  simp only [Complex.ofReal_natCast]
  change _ = _ * γ ^ e.val * ν ^ (e.val + 3 * l) * θ ^ k * (θ⁻¹) ^ (e.val + 3 * l) * _
  calc
    _ = probePrimeLocalCoefficient K p hp χ (e.val + 3 * l) k (j + 6 * m) *
        γ ^ e.val * ν ^ (e.val + 3 * l) * θ ^ k * (θ⁻¹) ^ (e.val + 3 * l) *
          ((Q ^ (-(1 / 2 + ξ))) ^ e.val * (Q ^ (-(1 + 3 * ξ))) ^ l *
            (Q ^ (-w)) ^ k * (Q ^ (-(6 * z))) ^ m) := by
      simp only [pow_add, pow_mul, mul_pow]
      ring
    _ = _ := by rw [hpow]

def probeBadPrimeSourceSeries (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (j : ℕ) (γ ν θ ξ w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' i : ℕ × (ℕ × ℕ),
    probeBadPrimeSourceTerm K p hp χ j γ ν θ ξ w z e i.2.1 i.1 i.2.2

theorem probeBadPrimeSourceSeries_eq (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (j : ℕ) (γ ν θ ξ w z : ℂ) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    probeBadPrimeSourceSeries K p hp χ j γ ν θ ξ w z =
      probeBadPrimeOriginalSeries K p hp χ j (probeBadFirstParameter Q γ ν θ ξ)
        (probeBadThetaParameter Q ν θ ξ) (ArtinMatthews.probeLocalW Q θ w)
        (ArtinMatthews.probeLocalV Q z) := by
  simp only [probeBadPrimeSourceSeries, probeBadPrimeOriginalSeries, probeBadPrimeWeight_eq_source]

theorem probeBadPrimeSource_norm_summable (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j)
    (γ ν θ ξ w z : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (hregion : ArtinMatthews.probeEulerRegion ξ.re w.re z.re) (e : Fin 2) :
    Summable (fun i : ℕ × (ℕ × ℕ) =>
      ‖probeBadPrimeSourceTerm K p hp.ne_zero χ j γ ν θ ξ w z e i.2.1 i.1 i.2.2‖) := by
  obtain ⟨hA, hV⟩ := probeBadParameters_small (Ideal.absNorm (Ideal.span {p}))
    γ ν θ ξ w z hγ hν hθ hcut hregion
  have H := probeBadPrimeOriginal_norm_summable K p hp χ hχ hminus j hj
    (probeBadFirstParameter (Ideal.absNorm (Ideal.span {p})) γ ν θ ξ)
    (probeBadThetaParameter (Ideal.absNorm (Ideal.span {p})) ν θ ξ)
    (ArtinMatthews.probeLocalW (Ideal.absNorm (Ideal.span {p})) θ w)
    (ArtinMatthews.probeLocalV (Ideal.absNorm (Ideal.span {p})) z)
    (by linarith) (by linarith) e
  simpa only [probeBadPrimeWeight_eq_source] using H

theorem probeBadPrimeSourceCorrection_regions (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j)
    (γ ν θ ξ w z : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (hregion : ArtinMatthews.probeEulerRegion ξ.re w.re z.re) :
    ‖(1 - ArtinMatthews.probeLocalV (Ideal.absNorm (Ideal.span {p})) z) *
      probeBadPrimeSourceSeries K p hp.ne_zero χ j γ ν θ ξ w z - 1‖ ≤
      36 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(1 / 4000 : ℝ)) := by
  obtain ⟨hA, hV⟩ := probeBadParameters_small (Ideal.absNorm (Ideal.span {p}))
    γ ν θ ξ w z hγ hν hθ hcut hregion
  rw [probeBadPrimeSourceSeries_eq,
    probeBadPrimeOriginalSeries_eq K p hp χ hχ hminus j hj _ _ _ _ (by linarith) (by linarith)]
  exact probeBadPrimeCorrection_regions K p hp χ hχ hminus j hj γ ν θ ξ w z hγ hν hθ hcut hregion

end
end ArtinMatthews.VaryingKummerAnalytic
