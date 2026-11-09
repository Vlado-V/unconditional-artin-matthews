module

public import ArtinMatthews.SourceHyperbolicH1Tests


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

def h1GradientAt (f : h1Tests ι 2) (p : ProductSpace ι) : H1Vector ι :=
  WithLp.toLp 2 (fun ij => (p ij.1 2 : ℂ) * productPartial f.val ij.1 ij.2 p)

theorem h1GradientAt_apply (f : h1Tests ι 2) (p : ProductSpace ι) (i : ι) (j : Fin 3) :
    h1GradientAt f p (i,j) = (p i 2 : ℂ) * productPartial f.val i j p := rfl

theorem h1GradientAt_continuous (f : h1Tests ι 2) : Continuous (h1GradientAt f) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι × Fin 3 => ℂ)).symm.continuous.comp
  apply continuous_pi
  intro ij
  exact (productHeightCLM ij.1).continuous.mul (product_test_partial_continuous f.prop.1 ij.1 ij.2)

theorem h1GradientAt_support (f : h1Tests ι 2) :
    tsupport (h1GradientAt f) ⊆ tsupport f.val := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  have hz : h1GradientAt f p = 0 := by
    apply (WithLp.equiv 2 (ι × Fin 3 → ℂ)).injective
    funext ij
    have hd : productPartial f.val ij.1 ij.2 p=0 := by
      rw [productPartial, fderiv_of_notMem_tsupport ℝ hn]
      rfl
    simp only [h1GradientAt, WithLp.equiv_apply, hd,
      mul_zero, WithLp.ofLp_zero, Pi.zero_apply]
  exact hp hz

theorem h1GradientAt_compact (f : h1Tests ι 2) : HasCompactSupport (h1GradientAt f) :=
  f.prop.2.1.of_isClosed_subset (isClosed_tsupport _) (h1GradientAt_support f)

def h1TestGradient (f : h1Tests ι 2) : H1Gradient ι :=
  (h1_compact_memLp (h1GradientAt_continuous f) (h1GradientAt_compact f)
    ((h1GradientAt_support f).trans f.prop.2.2) 2).toLp (h1GradientAt f)

theorem h1TestGradient_coe (f : h1Tests ι 2) :
    (h1TestGradient f : ProductSpace ι → H1Vector ι) =ᵐ[productVolume ι] h1GradientAt f :=
  (h1_compact_memLp (h1GradientAt_continuous f) (h1GradientAt_compact f)
    ((h1GradientAt_support f).trans f.prop.2.2) 2).coeFn_toLp

theorem h1GradientAt_add (f g : h1Tests ι 2) :
    h1GradientAt (f+g) = h1GradientAt f + h1GradientAt g := by
  funext p
  apply (WithLp.equiv 2 (ι × Fin 3 → ℂ)).injective
  funext ij
  simp only [h1GradientAt, productPartial, Submodule.coe_add,
    fderiv_add (f.prop.1.differentiable (by norm_num) p) (g.prop.1.differentiable (by norm_num) p),
    add_apply, WithLp.equiv_apply,
    WithLp.ofLp_add, Pi.add_apply, mul_add]

theorem h1GradientAt_smul (c : ℂ) (f : h1Tests ι 2) :
    h1GradientAt (c • f) = c • h1GradientAt f := by
  funext p
  apply (WithLp.equiv 2 (ι × Fin 3 → ℂ)).injective
  funext ij
  simp only [h1GradientAt, productPartial, Submodule.coe_smul,
    fderiv_const_smul (f.prop.1.differentiable (by norm_num) p),
    smul_apply, WithLp.equiv_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  ring

def h1TestGradientLinear (ι : Type*) [Fintype ι] : h1Tests ι 2 →ₗ[ℂ] H1Gradient ι where
  toFun := h1TestGradient
  map_add' f g := by
    apply Lp.ext
    filter_upwards [h1TestGradient_coe (f+g), h1TestGradient_coe f,
      h1TestGradient_coe g, Lp.coeFn_add (h1TestGradient f) (h1TestGradient g)] with p hfg hf hg ha
    simp only [hfg,ha,hf,hg,h1GradientAt_add,Pi.add_apply]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [h1TestGradient_coe (c•f), h1TestGradient_coe f,
      Lp.coeFn_smul c (h1TestGradient f)] with p hcf hf hs
    simp only [RingHom.id_apply,hcf,hs,hf,h1GradientAt_smul,Pi.smul_apply]

def h1ValueComponent (ij : ι × Fin 3) : H1Vector ι →L[ℂ] ℂ :=
  PiLp.proj 2 (fun _ : ι × Fin 3 => ℂ) ij

omit [Fintype ι] in
theorem h1ValueComponent_apply (ij : ι × Fin 3) (z : H1Vector ι) :
    h1ValueComponent ij z = z ij := rfl

def h1GradientComponent (ij : ι × Fin 3) : H1Gradient ι →L[ℂ] H1Mass ι :=
  (h1ValueComponent ij).compLpL 2 (productVolume ι)

theorem h1GradientComponent_coe (ij : ι × Fin 3) (g : H1Gradient ι) :
    (h1GradientComponent ij g : ProductSpace ι → ℂ) =ᵐ[productVolume ι]
      (fun p => g p ij) := by
  have h := (h1ValueComponent ij).coeFn_compLpL (p := 2) (μ := productVolume ι) g
  simpa only [h1GradientComponent,h1ValueComponent_apply] using! h

theorem h1GradientComponent_test (f : h1Tests ι 2) (ij : ι × Fin 3) :
    (h1GradientComponent ij (h1TestGradient f) : ProductSpace ι → ℂ) =ᵐ[productVolume ι]
      (fun p => (p ij.1 2 : ℂ) * productPartial f.val ij.1 ij.2 p) := by
  filter_upwards [h1GradientComponent_coe ij (h1TestGradient f), h1TestGradient_coe f] with p hc hf
  rw [hc,hf]
  rfl

end
end ArtinMatthews.SourceHyperbolicGreen
