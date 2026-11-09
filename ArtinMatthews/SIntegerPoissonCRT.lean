module

public import ArtinMatthews.SIntegerPrimeCRT
public import ArtinMatthews.ProbeIdealPoissonCRTHelpers


set_option backward.privateInPublic true
@[expose] public section

/-! The exact finite congruence-kernel factorization in the actual
S-integer ring. Every local quotient is proved finite from localization;
the source additive character is preserved through its CRT components. -/
namespace ArtinMatthews.SIntegerQuotient

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField BigOperators Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourceCRTGlobalSum (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (Ψ : AddChar ((PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P (fun i => k i + t i)) ℂ) (a h : PrincipalIntegerRing S₀)
    (W : ∀ i, ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (k i)) → ℂ)
    (V : ∀ i, ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (t i)) → ℂ) : ℂ :=
  ∑' d : ((PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P k),
    ∑' v : ((PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P t),
      if h - a * Quotient.out d ∈ crtModulus S₀ P k then
        (∏ i, W i (primeCRTEquiv S₀ P k hP d i)) *
        (∏ i, V i (primeCRTEquiv S₀ P t hP v i)) *
        Ψ (Ideal.Quotient.mk _ ((h - a * Quotient.out d) * Quotient.out v)) else 0

def sourceCRTLocalSum (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (Ψ : AddChar ((PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P (fun i => k i + t i)) ℂ) (a h : PrincipalIntegerRing S₀)
    (W : ∀ i, ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (k i)) → ℂ)
    (V : ∀ i, ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (t i)) → ℂ) (i : ι) : ℂ :=
  ∑' d : ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (k i)),
    ∑' v : ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (t i)),
      if h - a * Quotient.out d ∈ primePowerIdeal S₀ (P i) (k i) then
        W i d * V i v * probeCRTAddCharComponent (fun j => (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P j) (k j + t j))
          (primeCRTEquiv S₀ P (fun j => k j + t j) hP) Ψ i
          (Ideal.Quotient.mk _ ((h - a * Quotient.out d) * Quotient.out v)) else 0

theorem sourceCRTGlobalSum_factor
    (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (Ψ : AddChar ((PrincipalIntegerRing S₀) ⧸ crtModulus S₀ P (fun i => k i + t i)) ℂ) (a h : PrincipalIntegerRing S₀)
    (ha : a ∈ crtModulus S₀ P t)
    (W : ∀ i, ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (k i)) → ℂ)
    (V : ∀ i, ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (t i)) → ℂ) :
    sourceCRTGlobalSum S₀ P k t hP Ψ a h W V =
      ∏ i, sourceCRTLocalSum S₀ P k t hP Ψ a h W V i := by
  let I := crtModulus S₀ P k
  let J := crtModulus S₀ P t
  let eI := primeCRTEquiv S₀ P k hP
  let eJ := primeCRTEquiv S₀ P t hP
  let ψ := probeCRTAddCharComponent (fun j => (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P j) (k j + t j))
          (primeCRTEquiv S₀ P (fun j => k j + t j) hP) Ψ
  let : Finite ((PrincipalIntegerRing S₀) ⧸ I) := crtQuotient_finite S₀ P k hP hS
  let : Finite ((PrincipalIntegerRing S₀) ⧸ J) := crtQuotient_finite S₀ P t hP hS
  let : Fintype ((PrincipalIntegerRing S₀) ⧸ I) := Fintype.ofFinite _
  let : Fintype ((PrincipalIntegerRing S₀) ⧸ J) := Fintype.ofFinite _
  let : ∀ i, Finite ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (k i)) :=
    fun i => primePowerQuotient_finite S₀ (P i) (hS i) _
  let : ∀ i, Finite ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (t i)) :=
    fun i => primePowerQuotient_finite S₀ (P i) (hS i) _
  let : ∀ i, Fintype ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (k i)) := fun _ => Fintype.ofFinite _
  let : ∀ i, Fintype ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (t i)) := fun _ => Fintype.ofFinite _
  have hΨ (x : PrincipalIntegerRing S₀) : Ψ (Ideal.Quotient.mk _ x) =
      ∏ i, ψ i (Ideal.Quotient.mk (primePowerIdeal S₀ (P i) (k i + t i)) x) := by
    rw [probeCRTAddChar_factor (fun j => (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P j) (k j + t j))
      (primeCRTEquiv S₀ P (fun j => k j + t j) hP)]
    simp only [primeCRTEquiv_mk, ψ]
  let F := fun i (d : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (k i))
      (v : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (t i)) =>
    if h - a * Quotient.out d ∈ primePowerIdeal S₀ (P i) (k i) then W i d * V i v *
      ψ i (Ideal.Quotient.mk _ ((h - a * Quotient.out d) * Quotient.out v)) else 0
  have hpoint (d : (PrincipalIntegerRing S₀) ⧸ I) (v : (PrincipalIntegerRing S₀) ⧸ J) :
      (if h - a * Quotient.out d ∈ I then
        (∏ i, W i (eI d i)) * (∏ i, V i (eJ v i)) *
          Ψ (Ideal.Quotient.mk _ ((h - a * Quotient.out d) * Quotient.out v)) else 0) =
        ∏ i, F i (eI d i) (eJ v i) := by
    have hg (i : ι) : h - a * Quotient.out d ∈ primePowerIdeal S₀ (P i) (k i) ↔
        h - a * Quotient.out (eI d i) ∈ primePowerIdeal S₀ (P i) (k i) :=
      probeIdealPoisson_gate_congr _ a h _ _ (primeCRT_out_difference S₀ P k hP d i)
    have hall : h - a * Quotient.out d ∈ I ↔
        ∀ i, h - a * Quotient.out (eI d i) ∈ primePowerIdeal S₀ (P i) (k i) := by
      rw [crtModulus_mem_iff S₀ P k hP]
      exact forall_congr' hg
    by_cases hh : h - a * Quotient.out d ∈ I
    · rw [ite_eq_left hh]
      have hlocal := hall.mp hh
      have hphase (i : ι) :
          ψ i (Ideal.Quotient.mk _ ((h - a * Quotient.out d) * Quotient.out v)) =
            ψ i (Ideal.Quotient.mk _
              ((h - a * Quotient.out (eI d i)) * Quotient.out (eJ v i))) := by
        apply probeIdealPoisson_phase_congr_le
          (primePowerIdeal S₀ (P i) (k i)) (primePowerIdeal S₀ (P i) (t i)) (primePowerIdeal S₀ (P i) (k i + t i))
          (by rw [primePowerIdeal_add]) a h _ _ _ _
        · exact (crtModulus_mem_iff S₀ P t hP a).mp ha i
        · exact primeCRT_out_difference S₀ P k hP d i
        · exact primeCRT_out_difference S₀ P t hP v i
        · exact (hg i).mpr (hlocal i)
      change _ = ∏ i, if h - a * Quotient.out (eI d i) ∈ primePowerIdeal S₀ (P i) (k i) then _ else _
      simp only [ite_eq_left (hlocal _)]
      rw [hΨ]
      
      simp_rw [hphase]
      simp only [Finset.prod_mul_distrib]
    · rw [ite_eq_right hh]
      symm
      obtain ⟨i, hi⟩ := not_forall.mp (fun hh' => hh (hall.mpr hh'))
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact ite_eq_right hi
  unfold sourceCRTGlobalSum
  rw [tsum_fintype, ← eI.symm.toEquiv.sum_comp]
  calc
    _ = ∑ d : ∀ i, (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (k i),
        ∑ v : ∀ i, (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (t i), ∏ i, F i (d i) (v i) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [tsum_fintype, ← eJ.symm.toEquiv.sum_comp]
      apply Finset.sum_congr rfl
      intro v _
      have hd : eI (eI.symm.toEquiv d) = d := eI.apply_symm_apply d
      have hv : eJ (eJ.symm.toEquiv v) = v := eJ.apply_symm_apply v
      have H := hpoint (eI.symm.toEquiv d) (eJ.symm.toEquiv v)
      rw [hd, hv] at H
      have hd' : primeCRTEquiv S₀ P k hP (eI.symm.toEquiv d) = d := hd
      have hv' : primeCRTEquiv S₀ P t hP (eJ.symm.toEquiv v) = v := hv
      rw [hd', hv']
      exact H
    _ = _ := by
      simpa only [sourceCRTLocalSum, tsum_fintype, F, ψ] using probe_two_pi_sum F

end
end ArtinMatthews.SIntegerQuotient
