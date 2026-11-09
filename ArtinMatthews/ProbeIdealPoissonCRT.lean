module

public import ArtinMatthews.ProbeIdealPoissonCRTHelpers


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine finite global quotient factorization with the exact local
characters induced by the global ideal trace. No standard adelic-phase
identification or principal generator is assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def probeIdealPoissonGlobalSum (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (Ψ : AddChar ((𝓞 K) ⧸ probeIdealCRTModulus K P (fun i => k i + t i)) ℂ) (a h : 𝓞 K)
    (W : ∀ i, ((𝓞 K) ⧸ (P i).asIdeal ^ k i) → ℂ)
    (V : ∀ i, ((𝓞 K) ⧸ (P i).asIdeal ^ t i) → ℂ) : ℂ :=
  ∑' d : ((𝓞 K) ⧸ probeIdealCRTModulus K P k),
    ∑' v : ((𝓞 K) ⧸ probeIdealCRTModulus K P t),
      if h - a * Quotient.out d ∈ probeIdealCRTModulus K P k then
        (∏ i, W i (probeIdealCRTEquiv K P k hP d i)) *
        (∏ i, V i (probeIdealCRTEquiv K P t hP v i)) *
        Ψ (Ideal.Quotient.mk _ ((h - a * Quotient.out d) * Quotient.out v)) else 0

def probeIdealPoissonLocalSum (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (Ψ : AddChar ((𝓞 K) ⧸ probeIdealCRTModulus K P (fun i => k i + t i)) ℂ) (a h : 𝓞 K)
    (W : ∀ i, ((𝓞 K) ⧸ (P i).asIdeal ^ k i) → ℂ)
    (V : ∀ i, ((𝓞 K) ⧸ (P i).asIdeal ^ t i) → ℂ) (i : ι) : ℂ :=
  ∑' d : ((𝓞 K) ⧸ (P i).asIdeal ^ k i),
    ∑' v : ((𝓞 K) ⧸ (P i).asIdeal ^ t i),
      if h - a * Quotient.out d ∈ (P i).asIdeal ^ k i then
        W i d * V i v * probeCRTAddCharComponent (fun j => (𝓞 K) ⧸ (P j).asIdeal ^ (k j + t j))
          (probeIdealCRTEquiv K P (fun j => k j + t j) hP) Ψ i
          (Ideal.Quotient.mk _ ((h - a * Quotient.out d) * Quotient.out v)) else 0

theorem probeIdealPoissonGlobalSum_factor
    (P : ι → HeightOneSpectrum (𝓞 K)) (k t : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (Ψ : AddChar ((𝓞 K) ⧸ probeIdealCRTModulus K P (fun i => k i + t i)) ℂ) (a h : 𝓞 K)
    (ha : a ∈ probeIdealCRTModulus K P t)
    (W : ∀ i, ((𝓞 K) ⧸ (P i).asIdeal ^ k i) → ℂ)
    (V : ∀ i, ((𝓞 K) ⧸ (P i).asIdeal ^ t i) → ℂ) :
    probeIdealPoissonGlobalSum K P k t hP Ψ a h W V =
      ∏ i, probeIdealPoissonLocalSum K P k t hP Ψ a h W V i := by
  let I := probeIdealCRTModulus K P k
  let J := probeIdealCRTModulus K P t
  let eI := probeIdealCRTEquiv K P k hP
  let eJ := probeIdealCRTEquiv K P t hP
  let ψ := probeCRTAddCharComponent (fun j => (𝓞 K) ⧸ (P j).asIdeal ^ (k j + t j))
          (probeIdealCRTEquiv K P (fun j => k j + t j) hP) Ψ
  let : Finite ((𝓞 K) ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient
    (probeIdealCRTModulus_ne_zero K P k)
  let : Finite ((𝓞 K) ⧸ J) := Ring.HasFiniteQuotients.finiteQuotient
    (probeIdealCRTModulus_ne_zero K P t)
  let : Fintype ((𝓞 K) ⧸ I) := Fintype.ofFinite _
  let : Fintype ((𝓞 K) ⧸ J) := Fintype.ofFinite _
  let : ∀ i, Finite ((𝓞 K) ⧸ (P i).asIdeal ^ k i) :=
    fun i => Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ (P i).ne_bot)
  let : ∀ i, Finite ((𝓞 K) ⧸ (P i).asIdeal ^ t i) :=
    fun i => Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ (P i).ne_bot)
  let : ∀ i, Fintype ((𝓞 K) ⧸ (P i).asIdeal ^ k i) := fun _ => Fintype.ofFinite _
  let : ∀ i, Fintype ((𝓞 K) ⧸ (P i).asIdeal ^ t i) := fun _ => Fintype.ofFinite _
  have hΨ (x : 𝓞 K) : Ψ (Ideal.Quotient.mk _ x) =
      ∏ i, ψ i (Ideal.Quotient.mk ((P i).asIdeal ^ (k i + t i)) x) := by
    rw [probeCRTAddChar_factor (fun j => (𝓞 K) ⧸ (P j).asIdeal ^ (k j + t j))
      (probeIdealCRTEquiv K P (fun j => k j + t j) hP)]
    simp only [probeIdealCRTEquiv_mk, ψ]
  let F := fun i (d : (𝓞 K) ⧸ (P i).asIdeal ^ k i)
      (v : (𝓞 K) ⧸ (P i).asIdeal ^ t i) =>
    if h - a * Quotient.out d ∈ (P i).asIdeal ^ k i then W i d * V i v *
      ψ i (Ideal.Quotient.mk _ ((h - a * Quotient.out d) * Quotient.out v)) else 0
  have hpoint (d : (𝓞 K) ⧸ I) (v : (𝓞 K) ⧸ J) :
      (if h - a * Quotient.out d ∈ I then
        (∏ i, W i (eI d i)) * (∏ i, V i (eJ v i)) *
          Ψ (Ideal.Quotient.mk _ ((h - a * Quotient.out d) * Quotient.out v)) else 0) =
        ∏ i, F i (eI d i) (eJ v i) := by
    have hg (i : ι) : h - a * Quotient.out d ∈ (P i).asIdeal ^ k i ↔
        h - a * Quotient.out (eI d i) ∈ (P i).asIdeal ^ k i :=
      probeIdealPoisson_gate_congr _ a h _ _ (probeIdealCRT_out_difference K P k hP d i)
    have hall : h - a * Quotient.out d ∈ I ↔
        ∀ i, h - a * Quotient.out (eI d i) ∈ (P i).asIdeal ^ k i := by
      rw [probeIdealCRT_mem_iff K P k hP]
      exact forall_congr' hg
    by_cases hh : h - a * Quotient.out d ∈ I
    · rw [ite_eq_left hh]
      have hlocal := hall.mp hh
      have hphase (i : ι) :
          ψ i (Ideal.Quotient.mk _ ((h - a * Quotient.out d) * Quotient.out v)) =
            ψ i (Ideal.Quotient.mk _
              ((h - a * Quotient.out (eI d i)) * Quotient.out (eJ v i))) := by
        apply probeIdealPoisson_phase_congr_le
          ((P i).asIdeal ^ k i) ((P i).asIdeal ^ t i) ((P i).asIdeal ^ (k i + t i))
          (by rw [← pow_add]) a h _ _ _ _
        · exact (probeIdealCRT_mem_iff K P t hP a).mp ha i
        · exact probeIdealCRT_out_difference K P k hP d i
        · exact probeIdealCRT_out_difference K P t hP v i
        · exact (hg i).mpr (hlocal i)
      change _ = ∏ i, if h - a * Quotient.out (eI d i) ∈ (P i).asIdeal ^ k i then _ else _
      simp only [ite_eq_left (hlocal _)]
      rw [hΨ]
      
      simp_rw [hphase]
      simp only [Finset.prod_mul_distrib]
    · rw [ite_eq_right hh]
      symm
      obtain ⟨i, hi⟩ := not_forall.mp (fun hh' => hh (hall.mpr hh'))
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact ite_eq_right hi
  unfold probeIdealPoissonGlobalSum
  rw [tsum_fintype, ← eI.symm.toEquiv.sum_comp]
  calc
    _ = ∑ d : ∀ i, (𝓞 K) ⧸ (P i).asIdeal ^ k i,
        ∑ v : ∀ i, (𝓞 K) ⧸ (P i).asIdeal ^ t i, ∏ i, F i (d i) (v i) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [tsum_fintype, ← eJ.symm.toEquiv.sum_comp]
      apply Finset.sum_congr rfl
      intro v _
      have hd : eI (eI.symm.toEquiv d) = d := eI.apply_symm_apply d
      have hv : eJ (eJ.symm.toEquiv v) = v := eJ.apply_symm_apply v
      have H := hpoint (eI.symm.toEquiv d) (eJ.symm.toEquiv v)
      rw [hd, hv] at H
      have hd' : probeIdealCRTEquiv K P k hP (eI.symm.toEquiv d) = d := hd
      have hv' : probeIdealCRTEquiv K P t hP (eJ.symm.toEquiv v) = v := hv
      rw [hd', hv']
      exact H
    _ = _ := by
      simpa only [probeIdealPoissonLocalSum, tsum_fintype, F, ψ] using probe_two_pi_sum F

end
end ArtinMatthews.VaryingKummerAnalytic
