module

public import ArtinMatthews.ProbeLocalSurvivorIndex
public import ArtinMatthews.ProbePrimeGaussPhase


set_option backward.privateInPublic true
@[expose] public section

/-! The original local index and weights before the j=0 support is grouped.
Here a=Q^(-xi), b=Q^(-w), and V=Q^(-6z). -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probePrimeRawTerm (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (η θ a b V : ℂ)
    (i : ProbeLocalRawIndex) : ℂ :=
  let e : ℕ := if i.1 then 1 else 0
  let t := probeLocalIndexDegree i
  let q : ℂ := Ideal.absNorm (Ideal.span {p})
  let σ : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {p}))
  let γ := probePrimeGaussGamma K p hp χ 2
  let v := probePrimeGaussLocalVartheta K p hp χ η
  γ ^ e * v ^ t * (θ⁻¹) ^ t * (σ⁻¹) ^ e * (q⁻¹) ^ i.2.1 * a ^ t *
    (θ * b) ^ i.2.2.1 * V ^ i.2.2.2 *
      probePrimeLocalCoefficient K p hp χ t i.2.2.1 (6 * i.2.2.2)

def probePrimeRawLocalSeries (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (η θ a b V : ℂ) : ℂ :=
  ∑' i : ProbeLocalRawIndex, probePrimeRawTerm K p hp χ η θ a b V i

theorem probePrimeRawTerm_zero_of_coefficient (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (η θ a b V : ℂ)
    (i : ProbeLocalRawIndex)
    (hc : probePrimeLocalCoefficient K p hp χ (probeLocalIndexDegree i)
      i.2.2.1 (6 * i.2.2.2) = 0) :
    probePrimeRawTerm K p hp χ η θ a b V i = 0 := by
  simp only [probePrimeRawTerm, hc, mul_zero]

theorem probePrimeRawLocalSeries_reindex (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (η θ a b V : ℂ) :
    probePrimeRawLocalSeries K p hp.ne_zero χ η θ a b V =
      ∑' j : ProbeLocalSurvivor,
        probePrimeRawTerm K p hp.ne_zero χ η θ a b V (probeLocalSurvivorIndex j) := by
  apply probeLocal_supported_tsum K p hp χ hχ hminus
  exact probePrimeRawTerm_zero_of_coefficient K p hp.ne_zero χ η θ a b V

end

end ArtinMatthews.VaryingKummerAnalytic
