module

public import ArtinMatthews.ProbeCoherentPrimeGauss


set_option backward.privateInPublic true
@[expose] public section

/-! Exact lifting through several prime-power levels for the actual coherent
trace character, including the divisibility indicator and normalization. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeIntegerPrimeTrace_add_scale (p : 𝓞 K) (hp : p ≠ 0)
    (n k : ℕ) (x : 𝓞 K) :
    probeIntegerPrimeTrace K p hp (n + k) (p ^ k * x) =
      probeIntegerPrimeTrace K p hp n x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, pow_succ', mul_assoc, probeIntegerPrimeTrace_step, ih]

theorem probePrimePowerGauss_lift_add (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n k : ℕ) (h : 𝓞 K) :
    probePrimePowerGauss K p hp χ (n + k) (p ^ k * h) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ k *
        probePrimePowerGauss K p hp χ n h := by
  have he : Ideal.span {p * p ^ (n + k)} =
      Ideal.span {(p * p ^ n) * p ^ k} := by
    rw [pow_add, mul_assoc]
  let e := Ideal.quotEquivOfEq he
  have hemk (x : 𝓞 K) :
      e (Ideal.Quotient.mk (Ideal.span {p * p ^ (n + k)}) x) =
        Ideal.Quotient.mk (Ideal.span {(p * p ^ n) * p ^ k}) x :=
    Ideal.quotEquivOfEq_mk he x
  have heinv (x : 𝓞 K) :
      e.symm (Ideal.Quotient.mk (Ideal.span {(p * p ^ n) * p ^ k}) x) =
        Ideal.Quotient.mk (Ideal.span {p * p ^ (n + k)}) x := by
    apply e.injective
    rw [e.apply_symm_apply, hemk]
  let ψ : AddChar ((𝓞 K) ⧸ Ideal.span {(p * p ^ n) * p ^ k}) ℂ :=
    (probePrimePowerPhase K p hp (n + k)).compAddMonoidHom e.symm.toAddMonoidHom
  have hlow : probeIdealLowerChar (p * p ^ n) (p ^ k) ψ =
      probePrimePowerPhase K p hp n := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [probeIdealLowerChar_mk]
    change probePrimePowerPhase K p hp (n + k)
      (e.symm (Ideal.Quotient.mk _ (p ^ k * x))) = _
    rw [heinv, probePrimePowerPhase, probePrimePowerPhase,
      AddChar.inv_apply', AddChar.inv_apply', probePrimePowerProductTrace_mk,
      probePrimePowerProductTrace_mk, probeIntegerPrimeTrace_add_scale]
  have hreindex : probePrimePowerGauss K p hp χ (n + k) (p ^ k * h) =
      probeQuotientFourier (p * p ^ n) (p ^ k) ψ
        (fun x => χ (probeIdealReduction p (p ^ n) x)) (p ^ k * h) := by
    unfold probePrimePowerGauss probeQuotientFourier
    rw [← e.symm.toEquiv.tsum_eq]
    apply tsum_congr
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change χ (probeIdealReduction p (p ^ (n + k))
      (e.symm (Ideal.Quotient.mk _ x))) *
      probePrimePowerPhase K p hp (n + k)
        (Ideal.Quotient.mk _ (p ^ k * h) * e.symm (Ideal.Quotient.mk _ x)) = _
    rw [heinv]
    change χ (Ideal.Quotient.mk (Ideal.span {p}) x) * _ =
      χ (Ideal.Quotient.mk (Ideal.span {p}) x) * _
    congr 1
  rw [hreindex, probeQuotientFourier_lift (p * p ^ n) (p ^ k)
    (mul_ne_zero hp (pow_ne_zero n hp)) (pow_ne_zero k hp), hlow,
    ← Ideal.span_singleton_pow, map_pow, Nat.cast_pow]
  rfl

theorem probePrimePowerGauss_exactQuotient (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n k : ℕ) (h : 𝓞 K)
    (q : ∀ _hd : p ^ k ∣ h, {v : 𝓞 K // h = p ^ k * v}) :
    (if hd : p ^ k ∣ h then probePrimePowerGauss K p hp χ n (q hd).1 else 0) =
      ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ k)⁻¹ *
        probePrimePowerGauss K p hp χ (n + k) h := by
  have hQ : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp)
  by_cases hd : p ^ k ∣ h
  · rw [dite_eq_left hd]
    conv_rhs => rw [(q hd).2]
    rw [probePrimePowerGauss_lift_add, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero k hQ), one_mul]
  · rw [dite_eq_right hd]
    have hnd : ¬ p ^ (n + k) ∣ h := by
      intro he
      exact hd ((pow_dvd_pow p (Nat.le_add_left k n)).trans he)
    rw [probePrimePowerGauss_zero_off_support K p hp χ (n + k) h hnd, mul_zero]

end

end ArtinMatthews.VaryingKummerAnalytic
