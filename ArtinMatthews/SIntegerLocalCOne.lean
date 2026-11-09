module

public import ArtinMatthews.SIntegerSourceConvolution


set_option backward.privateInPublic true
@[expose] public section

/-! The literal one-outer-degree congruence and quotient in the standard
S-integer source coefficient. The quotient is an actual ring element. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

def principalDivide {R : Type*} [CommRing R] (a h : R) (hh : a ∣ h) : R := hh.choose

theorem principalDivide_spec {R : Type*} [CommRing R] (a h : R) (hh : a ∣ h) :
    h = a * principalDivide a h hh := hh.choose_spec

variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def standardLocalCOne (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n J : ℕ) : ℂ :=
  ∑' d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a},
    if hd : a ∣ a ^ J - a ^ (n + 1) * Quotient.out d then
      generatorResidueCharacter S₀ P hP a ha χ d *
        sourceGaussAt S₀ P hP a ha (χ ^ (n + 1)) n
          (principalDivide a (a ^ J - a ^ (n + 1) * Quotient.out d) hd)
    else 0

theorem standardLocalCOne_zero (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) :
    standardLocalCOne S₀ P hP a ha χ n 0 = 0 := by
  unfold standardLocalCOne
  apply Eq.trans (b := ∑' _d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a}, (0 : ℂ)) _ tsum_zero
  apply tsum_congr
  intro d
  have hn : ¬ a ∣ a ^ 0 - a ^ (n + 1) * Quotient.out d := by
    intro hd
    have hp : a ∣ a ^ (n + 1) * Quotient.out d := by
      refine ⟨a ^ n * Quotient.out d, ?_⟩
      rw [pow_succ']
      ring
    have h1 : a ∣ 1 := by
      simpa only [sub_add_cancel, pow_zero] using dvd_add hd hp
    exact (exterior_generator_nonunit S₀ P hP a ha) (isUnit_iff_dvd_one.mpr h1)
  exact dite_eq_right hn

theorem standardLocalCOne_succ (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n J : ℕ) :
    standardLocalCOne S₀ P hP a ha χ n (J + 1) =
      sourceScalarOne S₀ P hP a ha χ (χ ^ (n + 1)) n (a ^ J) := by
  unfold standardLocalCOne sourceScalarOne
  apply tsum_congr
  intro d
  have he : a ^ (J + 1) - a ^ (n + 1) * Quotient.out d =
      a * (a ^ J - a ^ n * Quotient.out d) := by
    simp only [pow_succ']
    ring
  have hd : a ∣ a ^ (J + 1) - a ^ (n + 1) * Quotient.out d := ⟨_, he⟩
  rw [dite_eq_left hd]
  have hdiv : principalDivide a (a ^ (J + 1) - a ^ (n + 1) * Quotient.out d) hd =
      a ^ J - a ^ n * Quotient.out d := by
    apply mul_left_cancel₀ (exterior_generator_ne_zero S₀ P a ha)
    exact (principalDivide_spec _ _ hd).symm.trans he
  rw [hdiv]

theorem residueTransformOnSource_pow_one (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (h : PrincipalIntegerRing S₀) :
    residueTransformOnSource S₀ P hP a ha (χ ^ n) 1 h =
      residueTransformOnSource S₀ P hP a ha χ n h := by
  rw [residueTransformOnSource_transport, residueTransformOnSource_transport]
  simp only [pow_one]

theorem standardLocalCOne_lift (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (hminus : χ (-1) = 1) (n J : ℕ) :
    standardLocalCOne S₀ P hP a ha χ n J =
      if n + 1 ≤ J then residueSourceTau S₀ P hP a ha χ *
        (Ideal.absNorm P.asIdeal : ℂ) ^ n *
        residueTransformOnSource S₀ P hP a ha χ n (a ^ (J - (n + 1))) else 0 := by
  cases J with
  | zero => rw [standardLocalCOne_zero]; simp
  | succ J =>
    rw [standardLocalCOne_succ, sourceScalarOne_eq S₀ P hP a ha hbad,
      MulChar.inv_apply_eq_inv', hminus, inv_one, one_mul, pow_succ, mul_inv_cancel_right]
    by_cases hnJ : n ≤ J
    · rw [ite_eq_left (Nat.succ_le_succ hnJ)]
      have hp : a ^ J = a ^ n * a ^ (J - n) := by rw [← pow_add, Nat.add_sub_of_le hnJ]
      rw [hp, sourceGaussAt_lift, residueTransformOnSource_pow_one]
      simp only [Nat.succ_sub_succ_eq_sub]
      ring
    · rw [ite_eq_right (fun h => hnJ (Nat.succ_le_succ_iff.mp h))]
      have hm : ¬ a ^ n ∣ a ^ J := by
        intro hd
        apply hnJ
        apply (generator_power_mem_iff S₀ P hP a ha n J).mp
        rw [generator_power_ideal S₀ P a ha n, Ideal.mem_span_singleton]
        exact hd
      rw [sourceGaussAt_zero_off_support S₀ P hP a ha hbad _ n _ hm, mul_zero]

end
end ArtinMatthews.SIntegerFourier
