module

public import ArtinMatthews.ProbePrimeLocalScalars


set_option backward.privateInPublic true
@[expose] public section

/-! Residue-field values and norms for the actual inverse trace phase. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField OAI.SevenEighths.FiniteFourier
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probePrimeResidueTransform_sixth (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (v : ℕ) (h : 𝓞 K) :
    probePrimeResidueTransform K p hp.ne_zero χ v h =
      if p ∣ h then (if 6 ∣ v then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1 else 0)
      else (χ ^ v)⁻¹ (Ideal.Quotient.mk _ h) * probePrimeTau K p hp.ne_zero (χ ^ v) := by
  let : (Ideal.span {p} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Field ((𝓞 K) ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ Ideal.span {p}) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Fintype ((𝓞 K) ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hψ : probePrimePhase K p hp.ne_zero ≠ 1 := by
    intro he
    have ht := probePrimePhase_primitive K p hp.ne_zero (one_ne_zero :
      (1 : ((𝓞 K) ⧸ Ideal.span {p})) ≠ 0)
    exact ht (by rw [AddChar.mulShift_one, he])
  have hc : Fintype.card ((𝓞 K) ⧸ Ideal.span {p}) = Ideal.absNorm (Ideal.span {p}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hz : Ideal.Quotient.mk (Ideal.span {p}) h = 0 ↔ p ∣ h := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  simpa only [probePrimeResidueTransform, probePrimeTau, tsum_fintype,
    probeResidueGauss, gaussSum, hz, hc] using
    probeResidueGauss_sixth χ hχ (probePrimePhase K p hp.ne_zero) hψ v
      (Ideal.Quotient.mk (Ideal.span {p}) h)

theorem probePrimeTau_principal (p : 𝓞 K) (hp : Prime p) :
    probePrimeTau K p hp.ne_zero 1 = -1 := by
  let : (Ideal.span {p} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Field ((𝓞 K) ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ Ideal.span {p}) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Fintype ((𝓞 K) ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hψ : probePrimePhase K p hp.ne_zero ≠ 1 := by
    intro he
    have ht := probePrimePhase_primitive K p hp.ne_zero (one_ne_zero :
      (1 : ((𝓞 K) ⧸ Ideal.span {p})) ≠ 0)
    exact ht (by rw [AddChar.mulShift_one, he])
  simpa only [probePrimeTau, tsum_fintype, gaussSum] using gaussSum_one_left hψ

theorem probePrimeTau_norm (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) :
    ‖probePrimeTau K p hp.ne_zero χ‖ = Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
  let : (Ideal.span {p} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Field ((𝓞 K) ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ Ideal.span {p}) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Fintype ((𝓞 K) ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hc : Fintype.card ((𝓞 K) ⧸ Ideal.span {p}) = Ideal.absNorm (Ideal.span {p}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  simpa only [probePrimeTau, tsum_fintype, gaussSum, hc] using
    primitive_gaussSum_norm χ (primitiveOnIdeals_of_field χ hχ)
      (probePrimePhase K p hp.ne_zero) (probePrimePhase_primitive K p hp.ne_zero)

theorem probePrimeResidueTransform_prime_pow (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (v J : ℕ) :
    probePrimeResidueTransform K p hp.ne_zero χ v (p ^ J) =
      if J = 0 then probePrimeTau K p hp.ne_zero (χ ^ v)
      else if 6 ∣ v then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1 else 0 := by
  cases J with
  | zero =>
      rw [ite_eq_left rfl]
      simp only [probePrimeResidueTransform, pow_zero, map_one, one_mul,
        probePrimeTau]
  | succ J =>
      rw [probePrimeResidueTransform_sixth K p hp χ hχ,
        ite_eq_left (dvd_pow_self p (Nat.succ_ne_zero J)),
        ite_eq_right (Nat.succ_ne_zero J)]

end

end ArtinMatthews.VaryingKummerAnalytic
