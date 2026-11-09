module

public import ArtinMatthews.ProbeCoherentPrimeTrace
public import ArtinMatthews.ProbeLocalCharacterCancellation
public import ArtinMatthews.ProbeFiniteLocalGauss


set_option backward.privateInPublic true
@[expose] public section

/-! Exact prime-power lifting with the coherent trace phase.  The phase is
the inverse trace character, as in the local sum in source05. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField BigOperators Classical
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

private theorem probe_sum_pullback {R S : Type*} [AddGroup R] [AddGroup S]
    [Finite R] [Finite S] (f : R →+ S) (hf : Function.Surjective f) (F : S → ℂ) :
    (∑' x : R, F (f x)) = (Nat.card f.ker : ℂ) * ∑' y : S, F y := by
  let : Fintype R := Fintype.ofFinite _
  let : Fintype S := Fintype.ofFinite _
  let : Fintype f.ker := Fintype.ofFinite _
  rw [tsum_fintype, tsum_fintype, ← Fintype.sum_fiberwise' f F]
  have hc (y : S) : Fintype.card {x : R // f x = y} = Fintype.card f.ker :=
    Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf y)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc,
    Nat.card_eq_fintype_card]
  rw [Finset.mul_sum]

theorem probeQuotientFourier_lift (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (ψ : AddChar ((𝓞 K) ⧸ Ideal.span {a * b}) ℂ)
    (F : ((𝓞 K) ⧸ Ideal.span {a}) → ℂ) (k : 𝓞 K) :
    probeQuotientFourier a b ψ F (b * k) =
      (Ideal.absNorm (Ideal.span {b}) : ℂ) *
        ∑' x : ((𝓞 K) ⧸ Ideal.span {a}),
          F x * probeIdealLowerChar a b ψ (Ideal.Quotient.mk _ k * x) := by
  let : Finite ((𝓞 K) ⧸ Ideal.span {a}) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr ha)
  let : Finite ((𝓞 K) ⧸ Ideal.span {a * b}) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha hb))
  unfold probeQuotientFourier
  calc
    _ = ∑' x : ((𝓞 K) ⧸ Ideal.span {a * b}), F (probeIdealReduction a b x) *
        probeIdealLowerChar a b ψ (Ideal.Quotient.mk _ k * probeIdealReduction a b x) := by
      apply tsum_congr
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      congr 1
      change _ = probeIdealLowerChar a b ψ (Ideal.Quotient.mk _ k * Ideal.Quotient.mk _ x)
      rw [← map_mul (Ideal.Quotient.mk (Ideal.span {a})) k x,
        probeIdealLowerChar_mk, ← map_mul, mul_assoc]
    _ = _ := by
      have he := probe_sum_pullback (probeIdealReduction a b).toAddMonoidHom
        (probeIdealReduction_surjective a b)
        (fun x => F x * probeIdealLowerChar a b ψ (Ideal.Quotient.mk _ k * x))
      rw [probeIdealReduction_kernel_card K a b ha] at he
      exact he

variable (K)

def probePrimePowerProductTrace (p : 𝓞 K) (hp : p ≠ 0) (n : ℕ) :
    AddChar ((𝓞 K) ⧸ Ideal.span {p * p ^ n}) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (Ideal.span {p * p ^ n}).toAddSubgroup
      (probeIntegerPrimeTrace K p hp n).toAddMonoidHom
      (fun x hx => probeIntegerPrimeTrace_period K p hp n x (by
        change x ∈ Ideal.span {p * p ^ n} at hx
        simpa only [pow_succ'] using hx)))

theorem probePrimePowerProductTrace_mk (p : 𝓞 K) (hp : p ≠ 0) (n : ℕ) (x : 𝓞 K) :
    probePrimePowerProductTrace K p hp n (Ideal.Quotient.mk _ x) =
      probeIntegerPrimeTrace K p hp n x := rfl

theorem probePrimePowerProductTrace_primitive (p : 𝓞 K) (hp : p ≠ 0) (n : ℕ) :
    (probePrimePowerProductTrace K p hp n).IsPrimitive := by
  intro x hx he
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  rw [← pow_succ']
  apply probeIntegerPrimeTrace_annihilator K p hp n d
  intro y
  have ht := congrArg
    (fun χ : AddChar ((𝓞 K) ⧸ Ideal.span {p * p ^ n}) ℂ =>
      χ (Ideal.Quotient.mk _ y)) he
  simpa only [AddChar.mulShift_apply, ← map_mul, probePrimePowerProductTrace_mk,
    AddChar.one_apply] using ht

def probePrimePowerPhase (p : 𝓞 K) (hp : p ≠ 0) (n : ℕ) :
    AddChar ((𝓞 K) ⧸ Ideal.span {p * p ^ n}) ℂ :=
  (probePrimePowerProductTrace K p hp n)⁻¹

def probePrimePhase (p : 𝓞 K) (hp : p ≠ 0) :
    AddChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ :=
  (idealTraceAddChar K (Ideal.span {p}) (Ideal.span_singleton_eq_bot.not.mpr hp))⁻¹

theorem probePrimePowerPhase_primitive (p : 𝓞 K) (hp : p ≠ 0) (n : ℕ) :
    (probePrimePowerPhase K p hp n).IsPrimitive := by
  intro x hx
  rw [probePrimePowerPhase, AddChar.inv_mulShift, AddChar.mulShift_mulShift, neg_one_mul]
  exact probePrimePowerProductTrace_primitive K p hp n (neg_ne_zero.mpr hx)

theorem probePrimePhase_primitive (p : 𝓞 K) (hp : p ≠ 0) :
    (probePrimePhase K p hp).IsPrimitive := by
  intro x hx
  rw [probePrimePhase, AddChar.inv_mulShift, AddChar.mulShift_mulShift, neg_one_mul]
  exact idealTraceAddChar_isPrimitive K (Ideal.span {p})
    (Ideal.span_singleton_eq_bot.not.mpr hp) (neg_ne_zero.mpr hx)

theorem probePrimePowerPhase_lower (p : 𝓞 K) (hp : p ≠ 0) (n : ℕ) :
    probeIdealLowerChar p (p ^ n) (probePrimePowerPhase K p hp n) =
      probePrimePhase K p hp := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [probeIdealLowerChar_mk]
  rw [probePrimePowerPhase, probePrimePhase, AddChar.inv_apply', AddChar.inv_apply',
    probePrimePowerProductTrace_mk, probeIntegerPrimeTrace_scale, idealTraceAddChar_mk]

def probePrimePowerGauss (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : 𝓞 K) : ℂ :=
  probeQuotientFourier p (p ^ n) (probePrimePowerPhase K p hp n) χ h

theorem probePrimePowerGauss_support (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : 𝓞 K)
    (hG : probePrimePowerGauss K p hp χ n h ≠ 0) : p ^ n ∣ h :=
  probeQuotientFourier_support p (p ^ n) hp _ (probePrimePowerPhase_primitive K p hp n)
    χ h hG

theorem probePrimePowerGauss_zero_off_support (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : 𝓞 K)
    (hd : ¬ p ^ n ∣ h) : probePrimePowerGauss K p hp χ n h = 0 :=
  probeQuotientFourier_zero_off_support p (p ^ n) hp _
    (probePrimePowerPhase_primitive K p hp n) χ h hd

theorem probePrimePowerGauss_lift (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : 𝓞 K) :
    probePrimePowerGauss K p hp χ n (p ^ n * h) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
        ∑' x : ((𝓞 K) ⧸ Ideal.span {p}), χ x *
          probePrimePhase K p hp (Ideal.Quotient.mk _ h * x) := by
  rw [probePrimePowerGauss, probeQuotientFourier_lift p (p ^ n) hp (pow_ne_zero n hp),
    probePrimePowerPhase_lower]
  rw [← Ideal.span_singleton_pow, map_pow, Nat.cast_pow]

end

end ArtinMatthews.VaryingKummerAnalytic
