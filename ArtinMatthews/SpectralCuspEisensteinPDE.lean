module

public import ArtinMatthews.SpectralCuspEisensteinSecondSeries
public import ArtinMatthews.SpectralGamma0EisensteinPDE


set_option backward.privateInPublic true
@[expose] public section

/-! Actual all-source Eisenstein C² regularity and eigen-PDE in its convergent half-plane. -/
noncomputable section
open Set Filter
open scoped ContDiff MatrixGroups
namespace ArtinMatthews

theorem cuspEisensteinRowPlaneTerm_hyperbolic_pde (N : ℕ) (r₀ a₀ : SL(2,ℤ)) (s : ℂ)
    (v : Gamma0CuspEisensteinRows N r₀ a₀) (p : ℝ × ℝ) (hp : 0<p.2) :
    -((p.2:ℂ)^2)*spectralPlaneHessianTrace
      (fderiv ℝ (fderiv ℝ (cuspEisensteinRowPlaneTerm N r₀ a₀ s v)) p) =
        s*(1-s)*cuspEisensteinRowPlaneTerm N r₀ a₀ s v p :=
  eisensteinRowPower_hyperbolic_pde s _ _ (cuspEisensteinRow_coefficients_ne_zero N r₀ a₀ v) p hp

theorem cuspEisensteinRow_raw_tsum_hyperbolic_pde (N : ℕ) (r₀ a₀ : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    -((p.2:ℂ)^2)*spectralPlaneHessianTrace
      (fderiv ℝ (fderiv ℝ (fun q => ∑' v : Gamma0CuspEisensteinRows N r₀ a₀, cuspEisensteinRowPlaneTerm N r₀ a₀ s v q)) p) =
        s*(1-s)*(∑' v : Gamma0CuspEisensteinRows N r₀ a₀, cuspEisensteinRowPlaneTerm N r₀ a₀ s v p) := by
  obtain ⟨hsum,he⟩ := cuspEisensteinRowPlane_second_series N r₀ a₀ s hs p hp
  rw [he,spectralPlaneHessianTrace.map_tsum hsum]
  calc
    _ = ∑' v : Gamma0CuspEisensteinRows N r₀ a₀, -((p.2:ℂ)^2)*spectralPlaneHessianTrace
        (fderiv ℝ (fderiv ℝ (cuspEisensteinRowPlaneTerm N r₀ a₀ s v)) p) := (tsum_mul_left).symm
    _ = ∑' v : Gamma0CuspEisensteinRows N r₀ a₀, s*(1-s)*cuspEisensteinRowPlaneTerm N r₀ a₀ s v p :=
      tsum_congr (fun v => cuspEisensteinRowPlaneTerm_hyperbolic_pde N r₀ a₀ s v p hp)
    _ = _ := tsum_mul_left

theorem cuspEisensteinRowPlaneSum_hessian_pde (N : ℕ) (r₀ a₀ : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    -((p.2:ℂ)^2)*spectralPlaneHessianTrace (fderiv ℝ (fderiv ℝ (cuspEisensteinRowPlaneSum N r₀ a₀ s)) p) =
      s*(1-s)*cuspEisensteinRowPlaneSum N r₀ a₀ s p := by
  have he : cuspEisensteinRowPlaneSum N r₀ a₀ s = (1/2:ℂ) •
      (fun q => ∑' v : Gamma0CuspEisensteinRows N r₀ a₀, cuspEisensteinRowPlaneTerm N r₀ a₀ s v q) := rfl
  have hscale : fderiv ℝ (fderiv ℝ (cuspEisensteinRowPlaneSum N r₀ a₀ s)) p =
      (1/2:ℂ) • fderiv ℝ (fderiv ℝ
        (fun q => ∑' v : Gamma0CuspEisensteinRows N r₀ a₀, cuspEisensteinRowPlaneTerm N r₀ a₀ s v q)) p := by
    rw [he,fderiv_const_smul_field]
    exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (R := ℂ)
      (f := fderiv ℝ (fun q => ∑' v : Gamma0CuspEisensteinRows N r₀ a₀, cuspEisensteinRowPlaneTerm N r₀ a₀ s v q))
      (1/2:ℂ)) p
  rw [hscale]
  change -((p.2:ℂ)^2)*spectralPlaneHessianTrace ((1/2:ℂ) •
    fderiv ℝ (fderiv ℝ (fun q => ∑' v : Gamma0CuspEisensteinRows N r₀ a₀, cuspEisensteinRowPlaneTerm N r₀ a₀ s v q)) p) = _
  rw [spectralPlaneHessianTrace_smul]
  have h := cuspEisensteinRow_raw_tsum_hyperbolic_pde N r₀ a₀ s hs p hp
  change _ = s*(1-s)*((1/2:ℂ)*(∑' v : Gamma0CuspEisensteinRows N r₀ a₀, cuspEisensteinRowPlaneTerm N r₀ a₀ s v p))
  linear_combination (1/2:ℂ)*h

theorem cuspEisensteinRowPlaneSum_hyperbolic_pde (N : ℕ) (r₀ a₀ : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    spectralPlanePositiveHyperbolic (cuspEisensteinRowPlaneSum N r₀ a₀ s) p =
      s*(1-s)*cuspEisensteinRowPlaneSum N r₀ a₀ s p := by
  have hc := (cuspEisensteinRowPlaneSum_contDiffOn N r₀ a₀ s hs p hp).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  have hd := (hc.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableAt (by norm_num)
  rw [spectralPlanePositiveHyperbolic_eq_hessian _ p hd]
  exact cuspEisensteinRowPlaneSum_hessian_pde N r₀ a₀ s hs p hp

theorem cuspEisensteinRowPlaneSum_eq (N : ℕ) (r a : SL(2,ℤ)) (s : ℂ)
    (p : ℝ×ℝ) (hp : 0 < p.2) :
    cuspEisensteinRowPlaneSum N r a s p=cuspEisensteinRowSum N r a s ⟨Complex.mk p.1 p.2,hp⟩ := by
  unfold cuspEisensteinRowPlaneSum cuspEisensteinRowSum
  congr 1
  exact tsum_congr (fun v => cuspEisensteinRowPlaneTerm_eq N r a s v p hp)

def gamma0CuspEisensteinPlane (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) (p : ℝ×ℝ) : ℂ :=
  (gamma0CuspTrueWidth N a:ℂ)^(-s)*cuspEisensteinRowPlaneSum N 1 a s p

theorem gamma0CuspEisensteinPlane_eq (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (p : ℝ×ℝ) (hp : 0 < p.2) :
    gamma0CuspEisensteinPlane N a s p=gamma0CuspEisenstein N a s ⟨Complex.mk p.1 p.2,hp⟩ := by
  rw [gamma0CuspEisensteinPlane,cuspEisensteinRowPlaneSum_eq N 1 a s p hp]
  rfl

theorem gamma0CuspEisensteinPlane_C2 (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (hs : 1 < s.re) :
    ContDiffOn ℝ 2 (gamma0CuspEisensteinPlane N a s) {p : ℝ×ℝ | 0 < p.2} :=
  contDiffOn_const.mul (cuspEisensteinRowPlaneSum_contDiffOn N 1 a s hs)

theorem gamma0CuspEisenstein_spatial_C2 (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (hs : 1 < s.re) :
    ContDiffOn ℝ 2 (fun z : ℂ => gamma0CuspEisenstein N a s (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im} := by
  have hc := (gamma0CuspEisensteinPlane_C2 N a s hs).comp
    Complex.equivRealProdCLM.contDiff.contDiffOn
    (show MapsTo Complex.equivRealProdCLM {z : ℂ | 0 < z.im} {p : ℝ×ℝ | 0 < p.2} by
      intro z hz; exact hz)
  apply hc.congr
  intro z hz
  simp only [Function.comp_apply]
  rw [gamma0CuspEisensteinPlane_eq N a s (Complex.equivRealProdCLM z) hz,UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  rfl

theorem gamma0CuspEisensteinPlane_hessian_pde (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (p : ℝ×ℝ) (hp : 0 < p.2) :
    -((p.2:ℂ)^2)*spectralPlaneHessianTrace (fderiv ℝ (fderiv ℝ (gamma0CuspEisensteinPlane N a s)) p)=
      s*(1-s)*gamma0CuspEisensteinPlane N a s p := by
  have he : gamma0CuspEisensteinPlane N a s=(gamma0CuspTrueWidth N a:ℂ)^(-s) •
      cuspEisensteinRowPlaneSum N 1 a s := rfl
  have hscale : fderiv ℝ (fderiv ℝ (gamma0CuspEisensteinPlane N a s)) p=
      (gamma0CuspTrueWidth N a:ℂ)^(-s) •
        fderiv ℝ (fderiv ℝ (cuspEisensteinRowPlaneSum N 1 a s)) p := by
    rw [he,fderiv_const_smul_field]
    exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (R := ℂ)
      (f := fderiv ℝ (cuspEisensteinRowPlaneSum N 1 a s)) ((gamma0CuspTrueWidth N a:ℂ)^(-s))) p
  rw [hscale,spectralPlaneHessianTrace_smul]
  have h := cuspEisensteinRowPlaneSum_hessian_pde N 1 a s hs p hp
  change _=s*(1-s)*((gamma0CuspTrueWidth N a:ℂ)^(-s)*cuspEisensteinRowPlaneSum N 1 a s p)
  linear_combination (gamma0CuspTrueWidth N a:ℂ)^(-s)*h

theorem gamma0CuspEisenstein_classical_eigen_pde (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (gamma0CuspEisenstein N a s) z=
      s*(1-s)*gamma0CuspEisenstein N a s z := by
  have he (w : UpperHalfPlane) : gamma0CuspEisensteinPlane N a s (w.re,w.im)=gamma0CuspEisenstein N a s w := by
    rw [gamma0CuspEisensteinPlane_eq N a s _ w.im_pos]
    congr 1
  have hc := (gamma0CuspEisensteinPlane_C2 N a s hs (z.re,z.im) z.im_pos).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos)
  have hd := (hc.fderiv_right (by norm_num : (1:ℕ∞ω)+1 ≤ 2)).differentiableAt (by norm_num)
  rw [h2SectionPositiveLaplacian_representation _ _ he,spectralPlanePositiveHyperbolic_eq_hessian _ _ hd,
    gamma0CuspEisensteinPlane_hessian_pde N a s hs _ z.im_pos,he]

end ArtinMatthews
