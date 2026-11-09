module

public import ArtinMatthews.ProbeIdealSurvivorIndex
public import ArtinMatthews.ProbeIdealGaussPhase


set_option backward.privateInPublic true
@[expose] public section

/-! The original local index and weights before the j=0 support is grouped.
Here a=Q^(-xi), b=Q^(-w), and V=Q^(-6z). -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probeIdealRawTerm (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (η θ a b V : ℂ)
    (i : ProbeLocalRawIndex) : ℂ :=
  let e : ℕ := if i.1 then 1 else 0
  let t := probeLocalIndexDegree i
  let q : ℂ := Ideal.absNorm (P.asIdeal)
  let σ : ℂ := Real.sqrt (Ideal.absNorm (P.asIdeal))
  let γ := probeIdealGaussGamma K P χ 2
  let v := probeIdealGaussLocalVartheta K P χ η
  γ ^ e * v ^ t * (θ⁻¹) ^ t * (σ⁻¹) ^ e * (q⁻¹) ^ i.2.1 * a ^ t *
    (θ * b) ^ i.2.2.1 * V ^ i.2.2.2 *
      probeIdealLocalCoefficient K P χ t i.2.2.1 (6 * i.2.2.2)

def probeIdealRawLocalSeries (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (η θ a b V : ℂ) : ℂ :=
  ∑' i : ProbeLocalRawIndex, probeIdealRawTerm K P χ η θ a b V i

theorem probeIdealRawTerm_zero_of_coefficient (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (η θ a b V : ℂ)
    (i : ProbeLocalRawIndex)
    (hc : probeIdealLocalCoefficient K P χ (probeLocalIndexDegree i)
      i.2.2.1 (6 * i.2.2.2) = 0) :
    probeIdealRawTerm K P χ η θ a b V i = 0 := by
  simp only [probeIdealRawTerm, hc, mul_zero]

theorem probeIdealRawLocalSeries_reindex (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (η θ a b V : ℂ) :
    probeIdealRawLocalSeries K P χ η θ a b V =
      ∑' j : ProbeLocalSurvivor,
        probeIdealRawTerm K P χ η θ a b V (probeLocalSurvivorIndex j) := by
  apply probeIdeal_supported_tsum K P χ hχ hminus
  exact probeIdealRawTerm_zero_of_coefficient K P χ η θ a b V

end

end ArtinMatthews.VaryingKummerAnalytic
