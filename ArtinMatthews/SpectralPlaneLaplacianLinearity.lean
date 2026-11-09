module

public import ArtinMatthews.SpectralCuspEisensteinPDE


set_option backward.privateInPublic true
@[expose] public section

/-! Finite linearity of the actual second-order plane operator. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace ArtinMatthews

theorem spectralPlane_hessian_finset_sum {ι : Type*} (T : Finset ι)
    (F : ι → ℝ×ℝ → ℂ)
    (hF : ∀ i ∈ T, ContDiffOn ℝ 2 (F i) {p : ℝ×ℝ | 0 < p.2})
    (p : ℝ×ℝ) (hp : 0 < p.2) :
    fderiv ℝ (fderiv ℝ (fun q => ∑ i ∈ T, F i q)) p=
      ∑ i ∈ T, fderiv ℝ (fderiv ℝ (F i)) p := by
  have hd (i) (hi : i ∈ T) (q : ℝ×ℝ) (hq : 0 < q.2) :
      DifferentiableAt ℝ (F i) q :=
    ((hF i hi).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hq)).differentiableAt
      (by norm_num)
  have hdd (i) (hi : i ∈ T) : DifferentiableAt ℝ (fderiv ℝ (F i)) p :=
    (((hF i hi).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)).fderiv_right
      (by norm_num : (1:ℕ∞ω)+1 ≤ 2)).differentiableAt (by norm_num)
  have he : fderiv ℝ (fun q => ∑ i ∈ T, F i q) =ᶠ[𝓝 p]
      fun q => ∑ i ∈ T, fderiv ℝ (F i) q := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with q hq
    exact fderiv_fun_sum (fun i hi => hd i hi q hq)
  rw [he.fderiv_eq]
  exact fderiv_fun_sum hdd

theorem spectralPlanePositiveHyperbolic_finset_sum {ι : Type*} (T : Finset ι)
    (F : ι → ℝ×ℝ → ℂ)
    (hF : ∀ i ∈ T, ContDiffOn ℝ 2 (F i) {p : ℝ×ℝ | 0 < p.2})
    (p : ℝ×ℝ) (hp : 0 < p.2) :
    spectralPlanePositiveHyperbolic (fun q => ∑ i ∈ T, F i q) p=
      ∑ i ∈ T, spectralPlanePositiveHyperbolic (F i) p := by
  have hc := (ContDiffOn.sum hF).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  have hd := (hc.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num)
  rw [spectralPlanePositiveHyperbolic_eq_hessian _ p hd,
    spectralPlane_hessian_finset_sum T F hF p hp,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hc' := (hF i hi).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  exact (spectralPlanePositiveHyperbolic_eq_hessian _ p
    ((hc'.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num))).symm

theorem spectralPlanePositiveHyperbolic_smul (c : ℂ) (F : ℝ×ℝ → ℂ)
    (hF : ContDiffOn ℝ 2 F {p : ℝ×ℝ | 0 < p.2}) (p : ℝ×ℝ) (hp : 0 < p.2) :
    spectralPlanePositiveHyperbolic (c • F) p=c*spectralPlanePositiveHyperbolic F p := by
  have hc := hF.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  have hd := (hc.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num)
  have hfc : ContDiffOn ℝ 2 (c • F) {p : ℝ×ℝ | 0 < p.2} :=
    (contDiffOn_const : ContDiffOn ℝ 2 (fun _ : ℝ×ℝ => c) {p | 0 < p.2}).mul hF
  have hc' := hfc.contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  have hd' := (hc'.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num)
  rw [spectralPlanePositiveHyperbolic_eq_hessian _ p hd',
    spectralPlanePositiveHyperbolic_eq_hessian _ p hd,fderiv_const_smul_field]
  have he := congrFun (fderiv_const_smul_field (𝕜 := ℝ) (R := ℂ) (f := fderiv ℝ F) c) p
  rw [he]
  change -((p.2:ℂ)^2)*spectralPlaneHessianTrace (c • fderiv ℝ (fderiv ℝ F) p)=_
  rw [spectralPlaneHessianTrace_smul]
  ring

end ArtinMatthews
