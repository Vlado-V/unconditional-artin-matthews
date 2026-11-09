module

public import ArtinMatthews.SIntegerPrincipalQuotient
public import ArtinMatthews.ProbeIdealCRTTrace


set_option backward.privateInPublic true
@[expose] public section

/-! Chinese remaindering in the actual S-integer ring. Each local
quotient is finite and has its original ideal-prime-power cardinality;
no integral principal generator for the original prime is required. -/
namespace ArtinMatthews.SIntegerQuotient

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]

def primePowerIdeal (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) : Ideal (PrincipalIntegerRing S₀) :=
  (P.asIdeal ^ n).map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))

def crtModulus (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ) : Ideal (PrincipalIntegerRing S₀) :=
  ∏ i, primePowerIdeal S₀ (P i) (n i)

omit [Fintype ι] in
theorem primePowerIdeal_pairwise (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) :
    Pairwise (fun i j => IsCoprime (primePowerIdeal S₀ (P i) (n i)) (primePowerIdeal S₀ (P j) (n j))) := by
  intro i j hij
  rw [Ideal.isCoprime_iff_sup_eq, primePowerIdeal, primePowerIdeal,
    ← Ideal.map_sup, (HeightOneSpectrum.isCoprime_pow_of_ne _ _ (hP hij) _ _).sup_eq,
    Ideal.map_top]

theorem crtModulus_eq_iInf (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) :
    crtModulus S₀ P n = ⨅ i, primePowerIdeal S₀ (P i) (n i) := by
  simpa only [crtModulus, Finset.mem_univ, iInf_pos] using
    (Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) ((primePowerIdeal_pairwise S₀ P n hP).set_pairwise _))

def primeCRTEquiv (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) :
    ((PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P n) ≃+*
      ∀ i, (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i) :=
  (Ideal.quotEquivOfEq (crtModulus_eq_iInf S₀ P n hP)).trans
    (Ideal.quotientInfRingEquivPiQuotient _ (primePowerIdeal_pairwise S₀ P n hP))

theorem primeCRTEquiv_mk (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (x : PrincipalIntegerRing S₀) (i : ι) :
    primeCRTEquiv S₀ P n hP (Ideal.Quotient.mk _ x) i = Ideal.Quotient.mk _ x := by
  rw [primeCRTEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

theorem crtModulus_mem_iff (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (x : PrincipalIntegerRing S₀) :
    x ∈ crtModulus S₀ P n ↔ ∀ i, x ∈ primePowerIdeal S₀ (P i) (n i) := by
  rw [crtModulus_eq_iInf S₀ P n hP]
  exact Ideal.mem_iInf

theorem primeCRT_out_difference (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (z : (PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P n) (i : ι) :
    Quotient.out z - Quotient.out (primeCRTEquiv S₀ P n hP z i) ∈ primePowerIdeal S₀ (P i) (n i) := by
  apply Ideal.Quotient.eq.mp
  rw [← primeCRTEquiv_mk S₀ P n hP, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out]

theorem primePowerQuotient_finite (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀) (n : ℕ) :
    Finite ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P n) := by
  let : Finite ((𝓞 K) ⧸ P.asIdeal ^ n) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero n P.ne_bot)
  exact Finite.of_equiv _ (principalPrimePowerQuotientEquiv S₀ P hP n).toEquiv

theorem crtQuotient_finite (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀) :
    Finite ((PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P n) := by
  let : ∀ i, Finite ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i)) :=
    fun i => primePowerQuotient_finite S₀ (P i) (hS i) (n i)
  exact Finite.of_equiv _ (primeCRTEquiv S₀ P n hP).toEquiv.symm

theorem primePowerIdeal_add (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (k t : ℕ) :
    primePowerIdeal S₀ P (k + t) = primePowerIdeal S₀ P k * primePowerIdeal S₀ P t := by
  rw [primePowerIdeal, pow_add, Ideal.map_mul]
  rfl

theorem crtModulus_add (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ) :
    crtModulus S₀ P (fun i => k i + t i) = crtModulus S₀ P k * crtModulus S₀ P t := by
  simp only [crtModulus, primePowerIdeal_add, Finset.prod_mul_distrib]

theorem crtModulus_generator (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i}) :
    crtModulus S₀ P n = Ideal.span {∏ i, a i ^ n i} := by
  simp only [crtModulus, primePowerIdeal, generator_power_ideal S₀ _ _ (ha _)]
  exact Ideal.prod_span_singleton Finset.univ (fun i => a i ^ n i)

end
end ArtinMatthews.SIntegerQuotient
