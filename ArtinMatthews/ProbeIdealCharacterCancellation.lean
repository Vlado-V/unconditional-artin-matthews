module

public import ArtinMatthews.ProbeIdealPrimeGauss


set_option backward.privateInPublic true
@[expose] public section

/-! Primitive-character cancellation on powers of arbitrary prime ideals. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probeIdealOuterFourier (P : HeightOneSpectrum (𝓞 K)) (m : ℕ)
    (ψ : AddChar ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)) ℂ)
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (h : 𝓞 K) : ℂ :=
  ∑' x : ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)),
    χ (probeIdealResidueReduction K P (m + 1) (Nat.succ_pos m) x) *
      ψ (Ideal.Quotient.mk _ h * x)

theorem probeIdealOuterFourier_shift (P : HeightOneSpectrum (𝓞 K)) (m : ℕ)
    (ψ : AddChar ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)) ℂ)
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (h t : 𝓞 K) :
    probeIdealOuterFourier K P m ψ χ h =
      ψ (Ideal.Quotient.mk _ (h * probeIdealUniformizer P * t)) *
        probeIdealOuterFourier K P m ψ χ h := by
  let q : ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)) :=
    Ideal.Quotient.mk _ (probeIdealUniformizer P * t)
  have hq : probeIdealResidueReduction K P (m + 1) (Nat.succ_pos m) q = 0 := by
    change Ideal.Quotient.mk P.asIdeal (probeIdealUniformizer P * t) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (P.asIdeal.mul_mem_right t (probeIdealUniformizer_mem P))
  unfold probeIdealOuterFourier
  conv_lhs => rw [← (Equiv.addRight q).tsum_eq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  change χ (probeIdealResidueReduction K P (m + 1) _ (x + q)) *
    ψ (Ideal.Quotient.mk _ h * (x + q)) = _
  simp only [map_add, hq, add_zero, mul_add, AddChar.map_add_eq_mul]
  have he : Ideal.Quotient.mk (P.asIdeal ^ (m + 1)) h * q =
      Ideal.Quotient.mk _ (h * probeIdealUniformizer P * t) := by
    dsimp [q]
    rw [← map_mul]
    congr 1
    ring
  rw [he]
  ring

theorem probeIdealOuterFourier_support (P : HeightOneSpectrum (𝓞 K)) (m : ℕ)
    (ψ : AddChar ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)) ℂ) (hψ : ψ.IsPrimitive)
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (h : 𝓞 K)
    (hF : probeIdealOuterFourier K P m ψ χ h ≠ 0) : h ∈ P.asIdeal ^ m := by
  have hphase (t : 𝓞 K) : ψ
      (Ideal.Quotient.mk _ (h * probeIdealUniformizer P * t)) = 1 := by
    apply mul_right_cancel₀ hF
    rw [one_mul, ← probeIdealOuterFourier_shift]
  have hz : Ideal.Quotient.mk (P.asIdeal ^ (m + 1)) (h * probeIdealUniformizer P) = 0 := by
    by_contra hn
    apply hψ hn
    ext x
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [AddChar.mulShift_apply, ← map_mul, AddChar.one_apply] using hphase t
  apply (probeIdealUniformizer_pow_mul_mem_iff P m 1 h).mp
  simpa only [pow_one, mul_comm h] using Ideal.Quotient.eq_zero_iff_mem.mp hz

theorem probeIdealOuterFourier_annihilated (P : HeightOneSpectrum (𝓞 K))
    (m : ℕ) (hm : 0 < m)
    (ψ : AddChar ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)) ℂ) (hψ : ψ.IsPrimitive)
    (χ ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (h : 𝓞 K) :
    ξ (Ideal.Quotient.mk P.asIdeal h) * probeIdealOuterFourier K P m ψ χ (-h) = 0 := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  by_cases hF : probeIdealOuterFourier K P m ψ χ (-h) = 0
  · rw [hF, mul_zero]
  · have hmem := probeIdealOuterFourier_support K P m ψ hψ χ (-h) hF
    have hpm : h ∈ P.asIdeal := by
      simpa only [neg_neg] using
        P.asIdeal.neg_mem ((Ideal.pow_le_self (Nat.ne_of_gt hm)) hmem)
    have hz : Ideal.Quotient.mk P.asIdeal h = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpm
    rw [hz, MulChar.map_zero, zero_mul]

def probeIdealHigherMixedSum (P : HeightOneSpectrum (𝓞 K)) (m b : ℕ)
    (χ ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (ψ : AddChar ((𝓞 K) ⧸ P.asIdeal ^ ((m + 1) + b)) ℂ) (H : 𝓞 K) : ℂ :=
  ∑' v : ((𝓞 K) ⧸ P.asIdeal ^ ((m + 1) + b)),
    ξ (probeIdealResidueReduction K P (m + 1) (Nat.succ_pos m)
      (probePrimePowerReduction P ((m + 1) + b) (m + 1) (Nat.le_add_right _ _) v)) *
      ψ (Ideal.Quotient.mk _ H * v) *
      ∑' d : ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)),
        χ (probeIdealResidueReduction K P (m + 1) (Nat.succ_pos m) d) *
          ψ (-(probePrimePowerScale P (m + 1) b d * v))

theorem probeIdealHigherMixedSum_eq_zero (P : HeightOneSpectrum (𝓞 K))
    (m b : ℕ) (hm : 0 < m) (χ ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (ψ : AddChar ((𝓞 K) ⧸ P.asIdeal ^ ((m + 1) + b)) ℂ) (hψ : ψ.IsPrimitive)
    (H : 𝓞 K) : probeIdealHigherMixedSum K P m b χ ξ ψ H = 0 := by
  unfold probeIdealHigherMixedSum
  apply Eq.trans (b := ∑' _v : ((𝓞 K) ⧸ P.asIdeal ^ ((m + 1) + b)), (0 : ℂ)) _ tsum_zero
  apply tsum_congr
  intro v
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective v
  have he : (∑' d : ((𝓞 K) ⧸ P.asIdeal ^ (m + 1)),
      χ (probeIdealResidueReduction K P (m + 1) (Nat.succ_pos m) d) *
        ψ (-(probePrimePowerScale P (m + 1) b d * Ideal.Quotient.mk _ a))) =
      probeIdealOuterFourier K P m (probePrimePowerLowerChar P (m + 1) b ψ) χ (-a) := by
    unfold probeIdealOuterFourier
    apply tsum_congr
    intro d
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
    congr 1
    rw [probePrimePowerScale_mk, ← map_mul, ← map_neg]
    change ψ (Ideal.Quotient.mk _ (-(probeIdealUniformizer P ^ b * d * a))) =
      probePrimePowerLowerChar P (m + 1) b ψ
        (Ideal.Quotient.mk _ (-a) * Ideal.Quotient.mk _ d)
    rw [← map_mul, probePrimePowerLowerChar_mk]
    congr 2
    ring
  rw [he]
  have hz := probeIdealOuterFourier_annihilated K P m hm
    (probePrimePowerLowerChar P (m + 1) b ψ)
    (probePrimePowerLowerChar_primitive P (m + 1) b ψ hψ) χ ξ a
  change ξ (Ideal.Quotient.mk P.asIdeal a) * _ * _ = 0
  linear_combination ψ (Ideal.Quotient.mk _ H * Ideal.Quotient.mk _ a) * hz

end

end ArtinMatthews.VaryingKummerAnalytic
