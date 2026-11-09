module

public import ArtinMatthews.SIntegerPoissonCRT
public import ArtinMatthews.SIntegerStandardPhase


set_option backward.privateInPublic true
@[expose] public section

/-! The literal finite source F(s,A,h) over the actual S-integer ring,
with e_S rather than an arbitrary ideal-trace character. Its genuine
CRT factorization retains the exact induced local additive phases. -/
namespace ArtinMatthews.SIntegerQuotient

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.StandardAdelic ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourceFiniteSum (I J : Ideal (PrincipalIntegerRing S₀))
    (s A h : PrincipalIntegerRing S₀) (f g : PrincipalIntegerRing S₀ → ℂ) : ℂ :=
  ∑' d : (PrincipalIntegerRing S₀) ⧸ I, ∑' v : (PrincipalIntegerRing S₀) ⧸ J,
    if h - A * Quotient.out d ∈ I then
      f (Quotient.out d) * g (Quotient.out v) *
        sCharacter K (principalizingSet S₀)
          (((h - A * Quotient.out d : PrincipalIntegerRing S₀) : K) *
            (Quotient.out v : PrincipalIntegerRing S₀) / ((s : K) * (A : K))) else 0

def sourceFiniteF (s A h : PrincipalIntegerRing S₀) (f g : PrincipalIntegerRing S₀ → ℂ) : ℂ :=
  sourceFiniteSum S₀ (Ideal.span {s}) (Ideal.span {A}) s A h f g

def crtResidueWeight (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (W : ∀ i, ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i)) → ℂ)
    (x : PrincipalIntegerRing S₀) : ℂ := ∏ i, W i (Ideal.Quotient.mk _ x)

def sourceCRTPhase (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (b : PrincipalIntegerRing S₀) (hb : b ≠ 0)
    (hM : crtModulus S₀ P n = Ideal.span {b}) :
    AddChar ((PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P n) ℂ :=
  pullAddChar (Ideal.quotEquivOfEq hM)
    (sIntegerQuotientPhase K (principalizingSet S₀) b hb)

omit [DecidableEq ι] in
theorem sourceCRTPhase_mk (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (b : PrincipalIntegerRing S₀) (hb : b ≠ 0)
    (hM : crtModulus S₀ P n = Ideal.span {b}) (x : PrincipalIntegerRing S₀) :
    sourceCRTPhase S₀ P n b hb hM (Ideal.Quotient.mk _ x) =
      sCharacter K (principalizingSet S₀) ((x : K) / (b : K)) := by
  rw [sourceCRTPhase, pullAddChar_apply, Ideal.quotEquivOfEq_mk, sIntegerQuotientPhase_mk]

omit [DecidableEq ι] in
theorem sourceCRT_modulus_product (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (s A : PrincipalIntegerRing S₀)
    (hI : crtModulus S₀ P k = Ideal.span {s})
    (hJ : crtModulus S₀ P t = Ideal.span {A}) :
    crtModulus S₀ P (fun i => k i + t i) = Ideal.span {s * A} := by
  rw [crtModulus_add, hI, hJ, Ideal.span_singleton_mul_span_singleton]

omit [DecidableEq ι] in
theorem sourceFiniteSum_eq_CRT (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (s A h : PrincipalIntegerRing S₀) (hsA : s * A ≠ 0)
    (hM : crtModulus S₀ P (fun i => k i + t i) = Ideal.span {s * A})
    (W : ∀ i, ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (k i)) → ℂ)
    (V : ∀ i, ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (t i)) → ℂ) :
    sourceFiniteSum S₀ (crtModulus S₀ P k) (crtModulus S₀ P t) s A h
      (crtResidueWeight S₀ P k W) (crtResidueWeight S₀ P t V) =
    sourceCRTGlobalSum S₀ P k t hP
      (sourceCRTPhase S₀ P (fun i => k i + t i) (s * A) hsA hM) A h W V := by
  unfold sourceFiniteSum sourceCRTGlobalSum
  apply tsum_congr
  intro d
  apply tsum_congr
  intro v
  split_ifs
  · have hd : crtResidueWeight S₀ P k W (Quotient.out d) =
        ∏ i, W i (primeCRTEquiv S₀ P k hP d i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← primeCRTEquiv_mk S₀ P k hP, Ideal.Quotient.mk_out]
    have hv : crtResidueWeight S₀ P t V (Quotient.out v) =
        ∏ i, V i (primeCRTEquiv S₀ P t hP v i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← primeCRTEquiv_mk S₀ P t hP, Ideal.Quotient.mk_out]
    rw [hd, hv, sourceCRTPhase_mk]
    rfl
  · rfl

theorem sourceFiniteF_factor (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (s A h : PrincipalIntegerRing S₀) (hs : s ≠ 0) (hA : A ≠ 0)
    (hI : crtModulus S₀ P k = Ideal.span {s})
    (hJ : crtModulus S₀ P t = Ideal.span {A})
    (W : ∀ i, ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (k i)) → ℂ)
    (V : ∀ i, ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (t i)) → ℂ) :
    sourceFiniteF S₀ s A h (crtResidueWeight S₀ P k W) (crtResidueWeight S₀ P t V) =
      ∏ i, sourceCRTLocalSum S₀ P k t hP
        (sourceCRTPhase S₀ P (fun i => k i + t i) (s * A) (mul_ne_zero hs hA)
          (sourceCRT_modulus_product S₀ P k t s A hI hJ)) A h W V i := by
  have ha : A ∈ crtModulus S₀ P t := by
    rw [hJ]
    exact Ideal.mem_span_singleton_self A
  unfold sourceFiniteF
  rw [← hI, ← hJ, sourceFiniteSum_eq_CRT S₀ P k t hP s A h (mul_ne_zero hs hA)
    (sourceCRT_modulus_product S₀ P k t s A hI hJ)]
  exact sourceCRTGlobalSum_factor S₀ P k t hP hS _ A h ha W V

end
end ArtinMatthews.SIntegerQuotient
