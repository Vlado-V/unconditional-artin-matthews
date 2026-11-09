module

public import ArtinMatthews.ProbePrimeRawWeights


set_option backward.privateInPublic true
@[expose] public section

/-! Structural transport of a convergent survivor sum back to the actual
raw local index. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeLocal_hasSum_transport (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (f : ProbeLocalRawIndex → ℂ) (s : ℂ)
    (hzero : ∀ i, probePrimeLocalCoefficient K p hp.ne_zero χ (probeLocalIndexDegree i)
      i.2.2.1 (6 * i.2.2.2) = 0 → f i = 0)
    (hs : HasSum (fun j : ProbeLocalSurvivor => f (probeLocalSurvivorIndex j)) s) :
    HasSum f s := by
  apply (probeLocalSurvivorIndex_injective.hasSum_iff ?_).mp hs
  intro i hi
  apply hzero
  by_contra hc
  exact hi (probeLocalCoefficient_support K p hp χ hχ hminus i hc)

theorem probePrimeRaw_survivor_eq (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2)
    (η θ a b V : ℂ) (hθ : θ ^ 6 = 1) :
    (fun j : ProbeLocalSurvivor =>
      probePrimeRawTerm K p hp.ne_zero χ η θ a b V (probeLocalSurvivorIndex j)) =
      probeLocalSurvivorValue (Ideal.absNorm (Ideal.span {p}))
        ((probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
          (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6)
        (θ * b) (η * θ⁻¹ * a) V := by
  funext j
  exact probePrimeRawTerm_survivor K p hp χ hχ hminus hchar η θ a b V hθ j

end

end ArtinMatthews.VaryingKummerAnalytic
