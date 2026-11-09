module

public import ArtinMatthews.ProbeIdealPrimeGauss
public import ArtinMatthews.ProbeSexticGaussPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite-field values for every nonzero prime ideal. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeIdealResidueTransform_sixth (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6) (v : ℕ) (h : 𝓞 K) :
    probeIdealResidueTransform K P χ v h =
      if h ∈ P.asIdeal then (if 6 ∣ v then (Ideal.absNorm P.asIdeal : ℂ) - 1 else 0)
      else (χ ^ v)⁻¹ (Ideal.Quotient.mk P.asIdeal h) * probeIdealTau K P (χ ^ v) := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hψ : probeIdealResiduePhase K P ≠ 1 := by
    intro he
    have ht := probeIdealResiduePhase_primitive K P
      (one_ne_zero : (1 : ((𝓞 K) ⧸ P.asIdeal)) ≠ 0)
    exact ht (by rw [AddChar.mulShift_one, he])
  have hc : Fintype.card ((𝓞 K) ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  simpa only [probeIdealResidueTransform, probeIdealTau, tsum_fintype, probeResidueGauss,
    gaussSum, Ideal.Quotient.eq_zero_iff_mem, hc] using
    probeResidueGauss_sixth χ hχ (probeIdealResiduePhase K P) hψ v
      (Ideal.Quotient.mk P.asIdeal h)

theorem probeIdealTau_principal (P : HeightOneSpectrum (𝓞 K)) :
    probeIdealTau K P 1 = -1 := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hψ : probeIdealResiduePhase K P ≠ 1 := by
    intro he
    have ht := probeIdealResiduePhase_primitive K P
      (one_ne_zero : (1 : ((𝓞 K) ⧸ P.asIdeal)) ≠ 0)
    exact ht (by rw [AddChar.mulShift_one, he])
  simpa only [probeIdealTau, tsum_fintype, gaussSum] using gaussSum_one_left hψ

theorem probeIdealTau_norm (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : χ ≠ 1) :
    ‖probeIdealTau K P χ‖ = Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card ((𝓞 K) ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  simpa only [probeIdealTau, tsum_fintype, gaussSum, hc] using
    primitive_gaussSum_norm χ (primitiveOnIdeals_of_field χ hχ)
      (probeIdealResiduePhase K P) (probeIdealResiduePhase_primitive K P)

theorem probeIdealTau_inverse_pair (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6) (hminus : χ (-1) = 1) :
    probeIdealTau K P χ * probeIdealTau K P (χ ^ 5) = (Ideal.absNorm P.asIdeal : ℂ) := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card ((𝓞 K) ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  simpa only [probeIdealTau, tsum_fintype, gaussSum, hc] using
    probeSexticGauss_inverse_pair χ hχ hminus (probeIdealResiduePhase K P)
      (probeIdealResiduePhase_primitive K P)

theorem probeIdealResidueTransform_prime_pow (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6) (v J : ℕ) :
    probeIdealResidueTransform K P χ v (probeIdealUniformizer P ^ J) =
      if J = 0 then probeIdealTau K P (χ ^ v)
      else if 6 ∣ v then (Ideal.absNorm P.asIdeal : ℂ) - 1 else 0 := by
  cases J with
  | zero =>
    rw [ite_eq_left rfl]
    simp only [probeIdealResidueTransform, pow_zero, map_one, one_mul, probeIdealTau]
  | succ J =>
    have hm : probeIdealUniformizer P ^ (J + 1) ∈ P.asIdeal := by
      rw [pow_succ']
      exact P.asIdeal.mul_mem_right _ (probeIdealUniformizer_mem P)
    rw [probeIdealResidueTransform_sixth K P χ hχ, ite_eq_left hm,
      ite_eq_right (Nat.succ_ne_zero J)]

end

end ArtinMatthews.VaryingKummerAnalytic
