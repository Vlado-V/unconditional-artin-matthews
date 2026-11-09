module

public import ArtinMatthews.ProbeIdealLocalCoefficient
public import ArtinMatthews.ProbeBadPrimeSourceWeight


set_option backward.privateInPublic true
@[expose] public section

/-! The literal source coefficient and complex norm weight at any ideal prime. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def probeIdealSourceTerm (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ)
    (γ ν θ ξ w z : ℂ) (e : Fin 2) (l k m : ℕ) : ℂ :=
  probeIdealLocalCoefficient K P χ (e.val + 3 * l) k (j + 6 * m) *
    γ ^ e.val * ν ^ (e.val + 3 * l) * θ ^ k * (θ⁻¹) ^ (e.val + 3 * l) *
      (Ideal.absNorm P.asIdeal : ℂ) ^
        (-((e.val : ℂ) * (1 / 2 + ξ) + (l : ℂ) * (1 + 3 * ξ) + (k : ℂ) * w + (6 * m : ℂ) * z))

def probeIdealSourceWeight (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ)
    (A B W V : ℂ) (e : Fin 2) (l k m : ℕ) : ℂ :=
  probeIdealLocalCoefficient K P χ (e.val + 3 * l) k (j + 6 * m) *
    A ^ e.val * B ^ l * W ^ k * V ^ m

theorem probeIdealSourceWeight_eq_source (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ)
    (γ ν θ ξ w z : ℂ) (e : Fin 2) (l k m : ℕ) :
    let Q : ℝ := Ideal.absNorm P.asIdeal
    probeIdealSourceWeight K P χ j (probeBadFirstParameter Q γ ν θ ξ)
      (probeBadThetaParameter Q ν θ ξ) (ArtinMatthews.probeLocalW Q θ w)
      (ArtinMatthews.probeLocalV Q z) e l k m =
      probeIdealSourceTerm K P χ j γ ν θ ξ w z e l k m := by
  let Q : ℂ := Ideal.absNorm P.asIdeal
  have hQ : Q ≠ 0 := by
    dsimp only [Q]
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
  have hpow : (Q ^ (-(1 / 2 + ξ))) ^ e.val * (Q ^ (-(1 + 3 * ξ))) ^ l *
      (Q ^ (-w)) ^ k * (Q ^ (-(6 * z))) ^ m =
      Q ^ (-((e.val : ℂ) * (1 / 2 + ξ) + (l : ℂ) * (1 + 3 * ξ) + (k : ℂ) * w + (6 * m : ℂ) * z)) := by
    rw [← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
      ← Complex.cpow_add _ _ hQ, ← Complex.cpow_add _ _ hQ, ← Complex.cpow_add _ _ hQ]
    congr 1
    ring
  dsimp only
  unfold probeIdealSourceWeight probeBadFirstParameter probeBadThetaParameter
    ArtinMatthews.probeLocalW ArtinMatthews.probeLocalV probeIdealSourceTerm
  simp only [Complex.ofReal_natCast]
  change _ = _ * γ ^ e.val * ν ^ (e.val + 3 * l) * θ ^ k * (θ⁻¹) ^ (e.val + 3 * l) * _
  calc
    _ = probeIdealLocalCoefficient K P χ (e.val + 3 * l) k (j + 6 * m) *
        γ ^ e.val * ν ^ (e.val + 3 * l) * θ ^ k * (θ⁻¹) ^ (e.val + 3 * l) *
          ((Q ^ (-(1 / 2 + ξ))) ^ e.val * (Q ^ (-(1 + 3 * ξ))) ^ l *
            (Q ^ (-w)) ^ k * (Q ^ (-(6 * z))) ^ m) := by
      simp only [pow_add, pow_mul, mul_pow]
      ring
    _ = _ := by rw [hpow]

def probeIdealSourceSeries (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ) (γ ν θ ξ w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' i : ℕ × (ℕ × ℕ),
    probeIdealSourceTerm K P χ j γ ν θ ξ w z e i.2.1 i.1 i.2.2

end
end ArtinMatthews.VaryingKummerAnalytic
