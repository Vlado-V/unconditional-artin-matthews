module

public import ArtinMatthews.SpectralGamma0EisensteinSecondSeries
public import ArtinMatthews.SpectralSectionLaplacian


set_option backward.privateInPublic true
@[expose] public section

/-! The actual convergent Eisenstein series satisfies the classical hyperbolic eigen-PDE. -/
noncomputable section
open Set Filter
open scoped ContDiff
namespace ArtinMatthews

theorem gamma0Eisenstein_spatial_C2 (N : ℕ) (s : ℂ) (hs : 1<s.re) :
    ContDiffOn ℝ 2 (fun z : ℂ => gamma0Eisenstein N s (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0<z.im} := by
  have hmap : MapsTo Complex.equivRealProdCLM {z : ℂ | 0<z.im} {p : ℝ × ℝ | 0<p.2} := by
    intro z hz
    exact hz
  have hc := (gamma0EisensteinPlaneSum_contDiffOn N s hs).comp
    Complex.equivRealProdCLM.contDiff.contDiffOn hmap
  apply hc.congr
  intro z hz
  simp only [Function.comp_apply]
  rw [gamma0EisensteinPlaneSum_eq N s (Complex.equivRealProdCLM z) hz,
    UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  rfl

def spectralPlaneHessianTrace :
    ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.apply ℝ ℂ (1,0)).comp
      (ContinuousLinearMap.apply ℝ ((ℝ × ℝ) →L[ℝ] ℂ) (1,0)) +
    (ContinuousLinearMap.apply ℝ ℂ (0,1)).comp
      (ContinuousLinearMap.apply ℝ ((ℝ × ℝ) →L[ℝ] ℂ) (0,1))

theorem spectralPlaneHessianTrace_apply (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℂ) :
    spectralPlaneHessianTrace A = A (1,0) (1,0)+A (0,1) (0,1) := rfl

theorem spectralPlaneHessianTrace_smul (c : ℂ) (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℂ) :
    spectralPlaneHessianTrace (c • A) = c*spectralPlaneHessianTrace A := by
  simp [spectralPlaneHessianTrace_apply,smul_eq_mul,mul_add]

theorem spectralPlaneSecond_eq_hessian (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) p) (i : Fin 2) :
    spectralPlaneSecond f i p = fderiv ℝ (fderiv ℝ f) p (spectralPlaneDirection i) (spectralPlaneDirection i) := by
  have h := (ContinuousLinearMap.apply ℝ ℂ (spectralPlaneDirection i)).hasFDerivAt.comp p hf.hasFDerivAt
  have he := congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℂ => A (spectralPlaneDirection i)) h.fderiv
  simpa only [spectralPlaneSecond,Function.comp_def,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] using he

theorem spectralPlanePositiveHyperbolic_eq_hessian (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) p) :
    spectralPlanePositiveHyperbolic f p = -((p.2:ℂ)^2)*spectralPlaneHessianTrace (fderiv ℝ (fderiv ℝ f) p) := by
  simp only [spectralPlanePositiveHyperbolic,spectralPlanePositiveSecond,Fin.sum_univ_two,
    spectralPlaneSecond_eq_hessian f p hf,spectralPlaneDirection,spectralPlaneHessianTrace_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Complex.real_smul,Complex.ofReal_pow]
  ring

theorem gamma0EisensteinPlaneTerm_hyperbolic_pde (N : ℕ) (s : ℂ)
    (v : Gamma0EisensteinRows N) (p : ℝ × ℝ) (hp : 0<p.2) :
    -((p.2:ℂ)^2)*spectralPlaneHessianTrace
      (fderiv ℝ (fderiv ℝ (gamma0EisensteinPlaneTerm N s v)) p) =
        s*(1-s)*gamma0EisensteinPlaneTerm N s v p :=
  eisensteinRowPower_hyperbolic_pde s _ _ (gamma0EisensteinRow_coefficients_ne_zero N v) p hp

theorem gamma0Eisenstein_raw_tsum_hyperbolic_pde (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    -((p.2:ℂ)^2)*spectralPlaneHessianTrace
      (fderiv ℝ (fderiv ℝ (fun q => ∑' v : Gamma0EisensteinRows N, gamma0EisensteinPlaneTerm N s v q)) p) =
        s*(1-s)*(∑' v : Gamma0EisensteinRows N, gamma0EisensteinPlaneTerm N s v p) := by
  obtain ⟨hsum,he⟩ := gamma0EisensteinPlane_second_series N s hs p hp
  rw [he,spectralPlaneHessianTrace.map_tsum hsum]
  calc
    _ = ∑' v : Gamma0EisensteinRows N, -((p.2:ℂ)^2)*spectralPlaneHessianTrace
        (fderiv ℝ (fderiv ℝ (gamma0EisensteinPlaneTerm N s v)) p) := (tsum_mul_left).symm
    _ = ∑' v : Gamma0EisensteinRows N, s*(1-s)*gamma0EisensteinPlaneTerm N s v p :=
      tsum_congr (fun v => gamma0EisensteinPlaneTerm_hyperbolic_pde N s v p hp)
    _ = _ := tsum_mul_left

theorem gamma0EisensteinPlaneSum_hessian_pde (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    -((p.2:ℂ)^2)*spectralPlaneHessianTrace (fderiv ℝ (fderiv ℝ (gamma0EisensteinPlaneSum N s)) p) =
      s*(1-s)*gamma0EisensteinPlaneSum N s p := by
  have he : gamma0EisensteinPlaneSum N s = (1/2:ℂ) •
      (fun q => ∑' v : Gamma0EisensteinRows N, gamma0EisensteinPlaneTerm N s v q) := rfl
  have hscale : fderiv ℝ (fderiv ℝ (gamma0EisensteinPlaneSum N s)) p =
      (1/2:ℂ) • fderiv ℝ (fderiv ℝ
        (fun q => ∑' v : Gamma0EisensteinRows N, gamma0EisensteinPlaneTerm N s v q)) p := by
    rw [he,fderiv_const_smul_field]
    exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (R := ℂ)
      (f := fderiv ℝ (fun q => ∑' v : Gamma0EisensteinRows N, gamma0EisensteinPlaneTerm N s v q))
      (1/2:ℂ)) p
  rw [hscale]
  change -((p.2:ℂ)^2)*spectralPlaneHessianTrace ((1/2:ℂ) •
    fderiv ℝ (fderiv ℝ (fun q => ∑' v : Gamma0EisensteinRows N, gamma0EisensteinPlaneTerm N s v q)) p) = _
  rw [spectralPlaneHessianTrace_smul]
  have h := gamma0Eisenstein_raw_tsum_hyperbolic_pde N s hs p hp
  change _ = s*(1-s)*((1/2:ℂ)*(∑' v : Gamma0EisensteinRows N, gamma0EisensteinPlaneTerm N s v p))
  linear_combination (1/2:ℂ)*h

theorem gamma0EisensteinPlaneSum_hyperbolic_pde (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    spectralPlanePositiveHyperbolic (gamma0EisensteinPlaneSum N s) p =
      s*(1-s)*gamma0EisensteinPlaneSum N s p := by
  have hc := (gamma0EisensteinPlaneSum_contDiffOn N s hs p hp).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  have hd := (hc.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num)
  rw [spectralPlanePositiveHyperbolic_eq_hessian _ p hd]
  exact gamma0EisensteinPlaneSum_hessian_pde N s hs p hp

theorem gamma0Eisenstein_classical_eigen_pde (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (gamma0Eisenstein N s) z = s*(1-s)*gamma0Eisenstein N s z := by
  have he (w : UpperHalfPlane) : gamma0EisensteinPlaneSum N s (w.re,w.im) = gamma0Eisenstein N s w := by
    rw [gamma0EisensteinPlaneSum_eq N s _ w.im_pos]
    congr 1
  rw [h2SectionPositiveLaplacian_representation _ _ he,
    gamma0EisensteinPlaneSum_hyperbolic_pde N s hs _ z.im_pos,he]

end ArtinMatthews
