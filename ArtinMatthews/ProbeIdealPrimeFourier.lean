module

public import ArtinMatthews.ProbeIdealCoherentTrace


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Fourier support and lifting on arbitrary prime-ideal powers.
The modulus is P^n, not the principal ideal of the chosen uniformizer. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probeIdealPhase (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    AddChar ((𝓞 K) ⧸ P.asIdeal ^ n) ℂ := (probeIdealCoherentTrace K P n)⁻¹

theorem probeIdealPhase_primitive (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (probeIdealPhase K P n).IsPrimitive := by
  intro x hx
  rw [probeIdealPhase, AddChar.inv_mulShift, AddChar.mulShift_mulShift, neg_one_mul]
  exact probeIdealCoherentTrace_primitive K P n (neg_ne_zero.mpr hx)

theorem probeIdealPhase_scale_mk (P : HeightOneSpectrum (𝓞 K)) (n k : ℕ) (x : 𝓞 K) :
    probeIdealPhase K P (n + k)
      (Ideal.Quotient.mk _ (probeIdealUniformizer P ^ k * x)) =
        probeIdealPhase K P n (Ideal.Quotient.mk _ x) := by
  simp only [probeIdealPhase, AddChar.inv_apply', probeIdealCoherentTrace_scale_mk]

def probeIdealFourierSum (P : HeightOneSpectrum (𝓞 K)) (n k : ℕ)
    (F : ((𝓞 K) ⧸ P.asIdeal ^ n) → ℂ) (h : 𝓞 K) : ℂ :=
  ∑' x : ((𝓞 K) ⧸ P.asIdeal ^ (n + k)),
    F (probePrimePowerReduction P (n + k) n (Nat.le_add_right n k) x) *
      probeIdealPhase K P (n + k) (Ideal.Quotient.mk _ h * x)

theorem probeIdealFourierSum_shift (P : HeightOneSpectrum (𝓞 K)) (n k : ℕ)
    (F : ((𝓞 K) ⧸ P.asIdeal ^ n) → ℂ) (h t : 𝓞 K) :
    probeIdealFourierSum K P n k F h =
      probeIdealPhase K P (n + k)
        (Ideal.Quotient.mk _ (h * probeIdealUniformizer P ^ n * t)) *
          probeIdealFourierSum K P n k F h := by
  let q : ((𝓞 K) ⧸ P.asIdeal ^ (n + k)) :=
    Ideal.Quotient.mk _ (probeIdealUniformizer P ^ n * t)
  have hq : probePrimePowerReduction P (n + k) n (Nat.le_add_right n k) q = 0 := by
    change Ideal.Quotient.mk (P.asIdeal ^ n) (probeIdealUniformizer P ^ n * t) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((P.asIdeal ^ n).mul_mem_right t (probeIdealUniformizer_pow_mem P n))
  unfold probeIdealFourierSum
  conv_lhs => rw [← (Equiv.addRight q).tsum_eq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  change F (probePrimePowerReduction P (n + k) n _ (x + q)) *
    probeIdealPhase K P (n + k) (Ideal.Quotient.mk _ h * (x + q)) = _
  simp only [map_add, hq, add_zero, mul_add, AddChar.map_add_eq_mul]
  have he : Ideal.Quotient.mk (P.asIdeal ^ (n + k)) h * q =
      Ideal.Quotient.mk _ (h * probeIdealUniformizer P ^ n * t) := by
    dsimp [q]
    rw [← map_mul]
    congr 1
    ring
  rw [he]
  ring

theorem probeIdealFourierSum_support (P : HeightOneSpectrum (𝓞 K)) (n k : ℕ)
    (F : ((𝓞 K) ⧸ P.asIdeal ^ n) → ℂ) (h : 𝓞 K)
    (hF : probeIdealFourierSum K P n k F h ≠ 0) : h ∈ P.asIdeal ^ k := by
  have hphase (t : 𝓞 K) : probeIdealPhase K P (n + k)
      (Ideal.Quotient.mk _ (h * probeIdealUniformizer P ^ n * t)) = 1 := by
    apply mul_right_cancel₀ hF
    rw [one_mul, ← probeIdealFourierSum_shift]
  have hz : Ideal.Quotient.mk (P.asIdeal ^ (n + k))
      (h * probeIdealUniformizer P ^ n) = 0 := by
    by_contra hn
    apply probeIdealPhase_primitive K P (n + k) hn
    ext x
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [AddChar.mulShift_apply, ← map_mul, AddChar.one_apply] using hphase t
  apply (probeIdealUniformizer_pow_mul_mem_iff P k n h).mp
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
  simpa only [mul_comm h, Nat.add_comm] using hm

theorem probeIdealFourierSum_zero_off_support (P : HeightOneSpectrum (𝓞 K)) (n k : ℕ)
    (F : ((𝓞 K) ⧸ P.asIdeal ^ n) → ℂ) (h : 𝓞 K) (hh : h ∉ P.asIdeal ^ k) :
    probeIdealFourierSum K P n k F h = 0 := by
  by_contra hn
  exact hh (probeIdealFourierSum_support K P n k F h hn)

theorem probeIdealFourierSum_frequency_congr (P : HeightOneSpectrum (𝓞 K)) (n k : ℕ)
    (F : ((𝓞 K) ⧸ P.asIdeal ^ n) → ℂ) (h h' : 𝓞 K)
    (hh : h - h' ∈ P.asIdeal ^ (n + k)) :
    probeIdealFourierSum K P n k F h = probeIdealFourierSum K P n k F h' := by
  have he : Ideal.Quotient.mk (P.asIdeal ^ (n + k)) h = Ideal.Quotient.mk _ h' :=
    Ideal.Quotient.eq.mpr hh
  simp only [probeIdealFourierSum, he]

private theorem probe_ideal_tsum_pullback {A B : Type*} [AddGroup A] [AddGroup B]
    [Finite A] [Finite B] (f : A →+ B) (hf : Function.Surjective f) (F : B → ℂ) :
    (∑' x : A, F (f x)) = (Nat.card f.ker : ℂ) * ∑' y : B, F y := by
  let : Fintype A := Fintype.ofFinite _
  let : Fintype B := Fintype.ofFinite _
  let : Fintype f.ker := Fintype.ofFinite _
  rw [tsum_fintype, tsum_fintype, ← Fintype.sum_fiberwise' f F]
  have hc (y : B) : Fintype.card {x : A // f x = y} = Fintype.card f.ker :=
    Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf y)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc,
    Nat.card_eq_fintype_card]
  rw [Finset.mul_sum]

theorem probeIdealFourierSum_lift (P : HeightOneSpectrum (𝓞 K)) (n k : ℕ)
    (F : ((𝓞 K) ⧸ P.asIdeal ^ n) → ℂ) (h : 𝓞 K) :
    probeIdealFourierSum K P n k F (probeIdealUniformizer P ^ k * h) =
      (Ideal.absNorm P.asIdeal : ℂ) ^ k *
        ∑' x : ((𝓞 K) ⧸ P.asIdeal ^ n), F x *
          probeIdealPhase K P n (Ideal.Quotient.mk _ h * x) := by
  let : Finite ((𝓞 K) ⧸ P.asIdeal ^ n) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero n P.ne_bot)
  let : Finite ((𝓞 K) ⧸ P.asIdeal ^ (n + k)) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero (n + k) P.ne_bot)
  unfold probeIdealFourierSum
  calc
    _ = ∑' x : ((𝓞 K) ⧸ P.asIdeal ^ (n + k)),
        F (probePrimePowerReduction P (n + k) n (Nat.le_add_right n k) x) *
          probeIdealPhase K P n
            (Ideal.Quotient.mk _ h *
              probePrimePowerReduction P (n + k) n (Nat.le_add_right n k) x) := by
      apply tsum_congr
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      congr 1
      rw [probePrimePowerReduction_mk, ← map_mul, ← map_mul, mul_assoc,
        probeIdealPhase_scale_mk]
    _ = _ := by
      have he := probe_ideal_tsum_pullback
        (probePrimePowerReduction P (n + k) n (Nat.le_add_right n k)).toAddMonoidHom
        (probePrimePowerReduction_surjective P (n + k) n (Nat.le_add_right n k))
        (fun x => F x * probeIdealPhase K P n (Ideal.Quotient.mk _ h * x))
      rw [probePrimePowerReduction_kernel_card, Nat.cast_pow] at he
      exact he

end

end ArtinMatthews.VaryingKummerAnalytic
