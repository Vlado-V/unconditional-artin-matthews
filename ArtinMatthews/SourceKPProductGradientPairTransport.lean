module

public import ArtinMatthews.SourceKPCompactCorePairChart
public import ArtinMatthews.SourceKPArchProjectiveEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The native weighted gradient is linear in the differential. Polarizing
the checked energy isometry gives transport of its mixed inner products. -/
namespace ArtinMatthews
open NumberField Matrix SourceHyperbolicGreen SourceArchJacquet OAI.CubicEisenstein
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff InnerProductSpace BigOperators ComplexConjugate
noncomputable section

variable {ι : Type*} [Fintype ι]

def sourceProductGradientOfDifferential (x : ProductSpace ι) :
    (ProductSpace ι →L[ℝ] ℂ) →ₗ[ℂ] H1Vector ι where
  toFun d := WithLp.toLp 2 (fun ij : ι × Fin 3 => (x ij.1 2 : ℂ)*d (productDirection ij.1 ij.2))
  map_add' d e := by
    apply (WithLp.equiv 2 ((ι × Fin 3) → ℂ)).injective
    funext ij
    simp only [WithLp.equiv_apply,WithLp.ofLp_toLp,WithLp.ofLp_add,Pi.add_apply,_root_.add_apply,mul_add]
  map_smul' c d := by
    apply (WithLp.equiv 2 ((ι × Fin 3) → ℂ)).injective
    funext ij
    simp only [WithLp.equiv_apply,WithLp.ofLp_toLp,WithLp.ofLp_smul,Pi.smul_apply,_root_.smul_apply,smul_eq_mul,
      RingHom.id_apply]
    ring

theorem sourceProductGradientOfDifferential_norm_sq (f : ProductSpace ι → ℂ) (x : ProductSpace ι) :
    ‖sourceProductGradientOfDifferential x (fderiv ℝ f x)‖^2 = productGradientEnergy f x := by
  change ‖WithLp.toLp 2 (fun ij : ι × Fin 3 => (x ij.1 2 : ℂ)*productPartial f ij.1 ij.2 x)‖^2 = _
  rw [EuclideanSpace.norm_sq_eq]
  simp only [WithLp.ofLp_toLp,Fintype.sum_prod_type,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    sq_abs,productGradientEnergy,Finset.mul_sum]

theorem sourceProductGradientOfDifferential_inner (f g : ProductSpace ι → ℂ) (x : ProductSpace ι) :
    inner ℂ (sourceProductGradientOfDifferential x (fderiv ℝ f x))
      (sourceProductGradientOfDifferential x (fderiv ℝ g x)) = productGradientPair f g x := by
  change inner ℂ (WithLp.toLp 2 (fun ij : ι × Fin 3 => (x ij.1 2 : ℂ)*productPartial f ij.1 ij.2 x))
    (WithLp.toLp 2 (fun ij : ι × Fin 3 => (x ij.1 2 : ℂ)*productPartial g ij.1 ij.2 x)) = _
  rw [PiLp.inner_apply,Fintype.sum_prod_type]
  simp only [WithLp.ofLp_toLp,RCLike.inner_apply,productGradientPair,map_mul,Finset.mul_sum,starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.star_def,Complex.conj_ofReal]
  ring

theorem sourceProductGradientOfDifferential_continuousOn (f : ProductSpace ι → ℂ)
    (hf : ContDiffOn ℝ 1 f (productUpper ι)) :
    ContinuousOn (fun x => sourceProductGradientOfDifferential x (fderiv ℝ f x)) (productUpper ι) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι × Fin 3 => ℂ)).symm.continuous.comp_continuousOn
  apply continuousOn_pi.mpr
  intro ij
  change ContinuousOn (fun x => (x ij.1 2 : ℂ)*productPartial f ij.1 ij.2 x) (productUpper ι)
  apply (productHeightCLM ij.1).continuous.continuousOn.mul
  intro x hx
  exact (productPartial_continuousAt_C1 ((hf x hx).contDiffAt ((productUpper_isOpen _).mem_nhds hx))
    ij.1 ij.2).continuousWithinAt

private theorem productGradient_combo (x : ProductSpace ι) (f g : ProductSpace ι → ℂ) (c : ℂ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    sourceProductGradientOfDifferential x (fderiv ℝ (f+c • g) x) =
      sourceProductGradientOfDifferential x (fderiv ℝ f x)+c • sourceProductGradientOfDifferential x (fderiv ℝ g x) := by
  rw [fderiv_add hf (hg.const_smul c),fderiv_const_smul hg,map_add,map_smul]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCompactCoreGradientLift_differential {n : ℕ∞ω} (f : sourceKPCompactCore K hζ n)
    (b : SourceKPFiniteLevelFiber K hζ) (x : ProductSpace (InfinitePlace K)) :
    sourceKPCompactCoreGradientLift K hζ f b x =
      sourceProductGradientOfDifferential x (fderiv ℝ (sourceKPCompactChartPullback K hζ f.val b) x) := rfl

theorem sourceKPArchEuclideanAction_gradientInner (a : PGL(2, InfiniteAdeleRing K))
    (f g : ProductSpace (InfinitePlace K) → ℂ) (x : ProductSpace (InfinitePlace K))
    (hx : x ∈ productUpper (InfinitePlace K))
    (hf : DifferentiableAt ℝ f (sourceKPArchEuclideanAction K hζ a x))
    (hg : DifferentiableAt ℝ g (sourceKPArchEuclideanAction K hζ a x)) :
    let A := sourceKPArchEuclideanAction K hζ a
    inner ℂ (sourceProductGradientOfDifferential x (fderiv ℝ (f ∘ A) x))
      (sourceProductGradientOfDifferential x (fderiv ℝ (g ∘ A) x)) =
        inner ℂ (sourceProductGradientOfDifferential (A x) (fderiv ℝ f (A x)))
          (sourceProductGradientOfDifferential (A x) (fderiv ℝ g (A x))) := by
  dsimp only
  let A := sourceKPArchEuclideanAction K hζ a
  let U (v : ProductSpace (InfinitePlace K) → ℂ) := sourceProductGradientOfDifferential x (fderiv ℝ (v ∘ A) x)
  let V (v : ProductSpace (InfinitePlace K) → ℂ) := sourceProductGradientOfDifferential (A x) (fderiv ℝ v (A x))
  change inner ℂ (U f) (U g) = inner ℂ (V f) (V g)
  have hA : DifferentiableAt ℝ A x :=
    (sourceKPArchEuclideanAction_contDiffAt K hζ a x hx).differentiableAt (by simp)
  have hfA : DifferentiableAt ℝ (f ∘ A) x := hf.comp x hA
  have hgA : DifferentiableAt ℝ (g ∘ A) x := hg.comp x hA
  have hn (c : ℂ) : ‖U f+c • U g‖^2 = ‖V f+c • V g‖^2 := by
    dsimp only [U,V]
    rw [← productGradient_combo x (f ∘ A) (g ∘ A) c hfA hgA,
      ← productGradient_combo (A x) f g c hf hg]
    change ‖sourceProductGradientOfDifferential x (fderiv ℝ ((f+c • g) ∘ A) x)‖^2 = _
    rw [sourceProductGradientOfDifferential_norm_sq,sourceProductGradientOfDifferential_norm_sq]
    exact sourceKPArchEuclideanAction_gradientEnergy K hζ a (f+c • g) x hx (hf.add (hg.const_smul c))
  have hc (c : ℂ) : (‖U f+c • U g‖ : ℂ)^2 = (‖V f+c • V g‖ : ℂ)^2 := by
    exact_mod_cast hn c
  have h₁ := hc 1
  have h₂ := hc (-1)
  have h₃ := hc (-Complex.I)
  have h₄ := hc Complex.I
  simp only [one_smul,neg_smul,← sub_eq_add_neg] at h₁ h₂ h₃ h₄
  have hU := inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (U f) (U g)
  have hV := inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (V f) (V g)
  change inner ℂ (U f) (U g) = ((‖U f+U g‖ : ℂ)^2-(‖U f-U g‖ : ℂ)^2 +
    ((‖U f-Complex.I • U g‖ : ℂ)^2-(‖U f+Complex.I • U g‖ : ℂ)^2)*Complex.I)/4 at hU
  change inner ℂ (V f) (V g) = ((‖V f+V g‖ : ℂ)^2-(‖V f-V g‖ : ℂ)^2 +
    ((‖V f-Complex.I • V g‖ : ℂ)^2-(‖V f+Complex.I • V g‖ : ℂ)^2)*Complex.I)/4 at hV
  rw [hU,hV,h₁,h₂,h₃,h₄]

end
end ArtinMatthews
