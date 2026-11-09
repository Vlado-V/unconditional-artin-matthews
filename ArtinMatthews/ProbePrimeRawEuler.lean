module

public import ArtinMatthews.ProbeLocalSurvivorSum
public import ArtinMatthews.ProbeLocalHasSumTransport
public import Mathlib.Analysis.Normed.Module.FiniteDimension


set_option backward.privateInPublic true
@[expose] public section

/-! The original Bool x Nat x Nat x Nat local series has the source's good
rational factor, with its actual constructed local Gauss correction. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probePrimeRawLocal_hasSum (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2)
    (η θ a b V : ℂ) (hθ : θ ^ 6 = 1) (hV : ‖V‖ < 1) (hW : ‖θ * b‖ < 1)
    (hE : ‖(probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6 * V‖ < 1) :
    HasSum (probePrimeRawTerm K p hp.ne_zero χ η θ a b V)
      (ArtinMatthews.probeGoodLocalFactor (Ideal.absNorm (Ideal.span {p})) V (θ * b)
        (η * θ⁻¹ * a)
        ((probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
          (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6 * V)) := by
  have hq : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  have hs := probeLocalSurvivor_hasSum (Ideal.absNorm (Ideal.span {p}) : ℂ)
    ((probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6)
    (θ * b) (η * θ⁻¹ * a) V hq hV hW hE
  have ht : HasSum (fun j : ProbeLocalSurvivor =>
      probePrimeRawTerm K p hp.ne_zero χ η θ a b V (probeLocalSurvivorIndex j))
      (ArtinMatthews.probeGoodLocalFactor (Ideal.absNorm (Ideal.span {p})) V (θ * b)
        (η * θ⁻¹ * a)
        ((probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
          (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6 * V)) := by
    rw [probePrimeRaw_survivor_eq K p hp χ hχ hminus hchar η θ a b V hθ]
    exact hs
  exact probeLocal_hasSum_transport K p hp χ hχ hminus
    (probePrimeRawTerm K p hp.ne_zero χ η θ a b V) _
    (probePrimeRawTerm_zero_of_coefficient K p hp.ne_zero χ η θ a b V) ht

theorem probePrimeRawLocalSeries_eq (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2)
    (η θ a b V : ℂ) (hθ : θ ^ 6 = 1) (hV : ‖V‖ < 1) (hW : ‖θ * b‖ < 1)
    (hE : ‖(probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6 * V‖ < 1) :
    probePrimeRawLocalSeries K p hp.ne_zero χ η θ a b V =
      ArtinMatthews.probeGoodLocalFactor (Ideal.absNorm (Ideal.span {p})) V (θ * b)
        (η * θ⁻¹ * a)
        ((probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
          (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6 * V) :=
  (probePrimeRawLocal_hasSum K p hp χ hχ hminus hchar η θ a b V hθ hV hW hE).tsum_eq

theorem probePrimeRawLocal_summable_norm (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2)
    (η θ a b V : ℂ) (hθ : θ ^ 6 = 1) (hV : ‖V‖ < 1) (hW : ‖θ * b‖ < 1)
    (hE : ‖(probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6 * V‖ < 1) :
    Summable (fun i : ProbeLocalRawIndex => ‖probePrimeRawTerm K p hp.ne_zero χ η θ a b V i‖) :=
  (probePrimeRawLocal_hasSum K p hp χ hχ hminus hchar η θ a b V hθ hV hW hE).summable.norm

theorem probePrimeRawLocalNested_eq (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2)
    (η θ a b V : ℂ) (hθ : θ ^ 6 = 1) (hV : ‖V‖ < 1) (hW : ‖θ * b‖ < 1)
    (hE : ‖(probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6 * V‖ < 1) :
    (∑' e : Bool, ∑' l : ℕ, ∑' k : ℕ, ∑' r : ℕ,
      probePrimeRawTerm K p hp.ne_zero χ η θ a b V (e, l, k, r)) =
      ArtinMatthews.probeGoodLocalFactor (Ideal.absNorm (Ideal.span {p})) V (θ * b)
        (η * θ⁻¹ * a)
        ((probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
          (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6 * V) := by
  have hs := probePrimeRawLocal_hasSum K p hp χ hχ hminus hchar η θ a b V hθ hV hW hE
  have he : (∑' i : ProbeLocalRawIndex, probePrimeRawTerm K p hp.ne_zero χ η θ a b V i) =
      ∑' e : Bool, ∑' l : ℕ, ∑' k : ℕ, ∑' r : ℕ,
        probePrimeRawTerm K p hp.ne_zero χ η θ a b V (e, l, k, r) := by
    rw [hs.summable.tsum_prod]
    apply tsum_congr
    intro e
    rw [(hs.summable.prod_factor e).tsum_prod]
    apply tsum_congr
    intro l
    exact ((hs.summable.prod_factor e).prod_factor l).tsum_prod
  exact he.symm.trans hs.tsum_eq

theorem probePrimeRawLocalAtUnit_eq (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2)
    (u : ((𝓞 K) ⧸ Ideal.span {p})ˣ) (η a b V : ℂ)
    (hV : ‖V‖ < 1) (hb : ‖b‖ < 1)
    (hE : ‖(probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6 * V‖ < 1) :
    probePrimeRawLocalSeries K p hp.ne_zero χ η (χ u) a b V =
      ArtinMatthews.probeGoodLocalFactor (Ideal.absNorm (Ideal.span {p})) V (χ u * b)
        (η * (χ u)⁻¹ * a)
        ((probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
          (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 * a ^ 6 * V) := by
  have h6 : χ ^ 6 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [hχ])
  have hθ : (χ u) ^ 6 = 1 := by
    rw [← χ.pow_apply_coe, h6, MulChar.one_apply_coe]
  have hnorm : ‖χ u‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 6 ≠ 0)).mp
    rw [← norm_pow, hθ, norm_one]
  apply probePrimeRawLocalSeries_eq K p hp χ hχ hminus hchar η (χ u) a b V hθ hV _ hE
  rwa [norm_mul, hnorm, one_mul]

end

end ArtinMatthews.VaryingKummerAnalytic
