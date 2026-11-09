module

public import ArtinMatthews.SpectralStoneAllEnergyAtoms


set_option backward.privateInPublic true
@[expose] public section

/-! Separate the cuspidal coefficients of the actual full Stone atoms
with all their Hilbert basis multiplicities. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace ArtinMatthews

local instance stoneNativeCuspidalInner (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜:=ℂ) (E:=Gamma0RegionL2 N) (gamma0AllHeightCuspidalMassSpace N)

theorem gamma0CuspidalProjection_norm_sq_hasSum (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    HasSum (fun i : Gamma0AllHeightSpectralIndex N =>
      ‖inner ℂ u (gamma0FullCuspidalSpectralBasis N i).val‖^2) (‖gamma0CuspidalProjection N u‖^2) := by
  let a (i : Gamma0AllHeightSpectralIndex N) := inner ℂ u (gamma0FullCuspidalSpectralBasis N i).val
  have hterm (i : Gamma0AllHeightSpectralIndex N) :
      (a i*inner ℂ (gamma0FullCuspidalSpectralBasis N i).val u).re=‖a i‖^2 := by
    rw [← inner_conj_symm (gamma0FullCuspidalSpectralBasis N i).val u]
    change (a i*(starRingEnd ℂ) (a i)).re=_
    rw [mul_comm,← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  have h := Complex.reCLM.hasSum (gamma0CuspidalProjection_spectral_hasSum N u u)
  change HasSum (fun i => (a i*inner ℂ (gamma0FullCuspidalSpectralBasis N i).val u).re)
    (inner ℂ (gamma0CuspidalProjection N u) (gamma0CuspidalProjection N u)).re at h
  have hn := inner_self_eq_norm_sq (𝕜:=ℂ) (gamma0CuspidalProjection N u)
  change (inner ℂ (gamma0CuspidalProjection N u) (gamma0CuspidalProjection N u)).re=
    ‖gamma0CuspidalProjection N u‖^2 at hn
  simpa only [hterm,hn] using h

theorem gamma0CuspidalProjection_norm_sq_add_remainder (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    ‖u‖^2=‖gamma0CuspidalProjection N u‖^2+‖gamma0NoncuspidalRemainder N u‖^2 := by
  rw [← inner_self_eq_norm_sq (𝕜:=ℂ) u,← inner_self_eq_norm_sq (𝕜:=ℂ) (gamma0CuspidalProjection N u),
    ← inner_self_eq_norm_sq (𝕜:=ℂ) (gamma0NoncuspidalRemainder N u)]
  change (inner ℂ u u).re=(inner ℂ (gamma0CuspidalProjection N u) (gamma0CuspidalProjection N u)).re+
    (inner ℂ (gamma0NoncuspidalRemainder N u) (gamma0NoncuspidalRemainder N u)).re
  simpa only [Complex.add_re] using
    congrArg Complex.re (gamma0_mass_cuspidal_split N u u)

theorem gamma0AmbientAtom_cuspidal_coefficient (N : ℕ) [NeZero N]
    (u : Gamma0RegionL2 N) (l : ℝ) (i : Gamma0AllHeightSpectralIndex N) :
    inner ℂ (gamma0AmbientSpectralAtomVector N u l) (gamma0FullCuspidalSpectralBasis N i).val=
      if l=gamma0AllHeightGradientSpectralValue N i then
        inner ℂ u (gamma0FullCuspidalSpectralBasis N i).val else 0 := by
  let v := gamma0FullCuspidalSpectralBasis N i
  let a := gamma0AmbientSpectralAtomVector N u l
  have hv := gamma0FullCuspidalSpectralBasis_mem_ambient_eigenspace N i
  by_cases h : l=gamma0AllHeightGradientSpectralValue N i
  · rw [ite_eq_left h]
    have hw : v.val∈gamma0AmbientEnergyEigenspace N l := h.symm ▸ hv
    have hzero := inner_eq_zero_symm.mp (gamma0AmbientSpectralAtomVector_orthogonal N u v.val l
      ((mem_gamma0AmbientEnergyEigenspace_iff N l _).mp hw))
    change inner ℂ (u-a) v.val=0 at hzero
    rw [inner_sub_left,sub_eq_zero] at hzero
    exact hzero.symm
  · rw [ite_eq_right h]
    apply gamma0AmbientEnergyEigenspace_orthogonal_of_ne N h _ hv
    exact (mem_gamma0AmbientEnergyEigenspace_iff N l a).mpr (gamma0AmbientSpectralAtomVector_green N u l)

theorem gamma0AmbientAtomNormSq_cuspidal_sum (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    (∑' l : Ici (0:ℝ),ENNReal.ofReal (‖gamma0CuspidalProjection N
      (gamma0AmbientSpectralAtomVector N u (l:ℝ))‖^2))=
      ENNReal.ofReal (‖gamma0CuspidalProjection N u‖^2) := by
  let L := Ici (0:ℝ)
  let a (l : L) := gamma0AmbientSpectralAtomVector N u (l:ℝ)
  let b (i : Gamma0AllHeightSpectralIndex N) := (gamma0FullCuspidalSpectralBasis N i).val
  let e (i : Gamma0AllHeightSpectralIndex N) : L :=
    ⟨gamma0AllHeightGradientSpectralValue N i,gamma0AllHeightGradientSpectralValue_nonneg N i⟩
  have hp (v : Gamma0RegionL2 N) :
      ENNReal.ofReal (‖gamma0CuspidalProjection N v‖^2)=
        ∑' i : Gamma0AllHeightSpectralIndex N,ENNReal.ofReal (‖inner ℂ v (b i)‖^2) := by
    have h := gamma0CuspidalProjection_norm_sq_hasSum N v
    rw [← h.tsum_eq,ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h.summable]
  change (∑' l : L,ENNReal.ofReal (‖gamma0CuspidalProjection N (a l)‖^2))=_
  simp_rw [hp]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro i
  have h (l : L) :
      inner ℂ (a l) (b i)=if l=e i then inner ℂ u (b i) else 0 := by
    have h' : ((l:ℝ)=gamma0AllHeightGradientSpectralValue N i) ↔ l=e i :=
      ⟨fun he => Subtype.ext he,fun he => congrArg Subtype.val he⟩
    simpa only [a,b,h'] using gamma0AmbientAtom_cuspidal_coefficient N u (l:ℝ) i
  simp_rw [h]
  rw [tsum_eq_single (e i)]
  · rw [ite_eq_left rfl]
  · intro l hl
    rw [ite_eq_right hl,norm_zero,zero_pow (by decide),ENNReal.ofReal_zero]

theorem gamma0AmbientResidualAtomNormSq_summable (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    Summable (fun l : Ici (0:ℝ) =>
      ‖gamma0NoncuspidalRemainder N (gamma0AmbientSpectralAtomVector N u (l:ℝ))‖^2) := by
  apply (gamma0AmbientAtomNormSq_summable N u).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro l
  rw [gamma0CuspidalProjection_norm_sq_add_remainder N (gamma0AmbientSpectralAtomVector N u (l:ℝ))]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem gamma0AmbientAtomNormSq_sum_split (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    (∑' l : Ici (0:ℝ),‖gamma0AmbientSpectralAtomVector N u (l:ℝ)‖^2)=
      ‖gamma0CuspidalProjection N u‖^2+
      ∑' l : Ici (0:ℝ),‖gamma0NoncuspidalRemainder N (gamma0AmbientSpectralAtomVector N u (l:ℝ))‖^2 := by
  let L := Ici (0:ℝ)
  let a (l : L) := gamma0AmbientSpectralAtomVector N u (l:ℝ)
  let b (l : L) := ‖gamma0CuspidalProjection N (a l)‖^2
  let r (l : L) := ‖gamma0NoncuspidalRemainder N (a l)‖^2
  have hEq (l : L) : ‖a l‖^2=b l+r l := gamma0CuspidalProjection_norm_sq_add_remainder N (a l)
  have hB : Summable b := (gamma0AmbientAtomNormSq_summable N u).of_nonneg_of_le
    (fun _ => sq_nonneg _) (fun l => by rw [hEq]; exact le_add_of_nonneg_right (sq_nonneg _))
  have hR : Summable r := gamma0AmbientResidualAtomNormSq_summable N u
  have hBsum : (∑' l : L,b l)=‖gamma0CuspidalProjection N u‖^2 := by
    have h := gamma0AmbientAtomNormSq_cuspidal_sum N u
    change (∑' l : L,ENNReal.ofReal (b l))=_ at h
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hB] at h
    simpa only [ENNReal.toReal_ofReal (tsum_nonneg (fun _ => sq_nonneg _)),
      ENNReal.toReal_ofReal (sq_nonneg _)] using congrArg ENNReal.toReal h
  change (∑' l : L,‖a l‖^2)=‖gamma0CuspidalProjection N u‖^2+∑' l : L,r l
  simp_rw [hEq]
  rw [hB.tsum_add hR,hBsum]

theorem gamma0CompactStoneNoncuspidalPlancherel (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    ‖gamma0NoncuspidalRemainder N (gamma0SmoothSeedMass N ψ)‖^2=
      (∫ t in Ioi 0,gamma0StoneFrequencyDensity N ψ t)+
      ∑' l : Ici (0:ℝ),‖gamma0NoncuspidalRemainder N
        (gamma0AmbientSpectralAtomVector N (gamma0SmoothSeedMass N ψ) (l:ℝ))‖^2 := by
  have h := gamma0CompactStonePlancherel_all_atoms N ψ
  rw [gamma0AmbientAtomNormSq_sum_split N,gamma0CuspidalProjection_norm_sq_add_remainder N] at h
  linarith only [h]

end ArtinMatthews
