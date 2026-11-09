module

public import ArtinMatthews.SourceKPCompactCoreEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Pointwise linear native gradients for the actual compact scalar core. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCompactChartPullback_differentiableAt (f : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) (x : ProductSpace (InfinitePlace K))
    (hx : x ∈ productUpper (InfinitePlace K)) :
    DifferentiableAt ℝ (sourceKPCompactChartPullback K hζ f.val b) x :=
  ((f.prop.2.2 b x hx).contDiffAt ((productUpper_isOpen _).mem_nhds hx)).differentiableAt (by norm_num)

def sourceKPCompactCoreGradientLiftLinear (b : SourceKPFiniteLevelFiber K hζ)
    (x : ProductSpace (InfinitePlace K)) (hx : x ∈ productUpper (InfinitePlace K)) :
    sourceKPCompactC2Core K hζ →ₗ[ℂ] H1Vector (InfinitePlace K) where
  toFun f := sourceKPCompactCoreGradientLift K hζ f b x
  map_add' f g := by
    have hf := sourceKPCompactChartPullback_differentiableAt K hζ f b x hx
    have hg := sourceKPCompactChartPullback_differentiableAt K hζ g b x hx
    apply (WithLp.equiv 2 ((InfinitePlace K × Fin 3) → ℂ)).injective
    funext ij
    simp only [sourceKPCompactCoreGradientLift,productPartial,Submodule.coe_add,
      sourceKPCompactChartPullback_add,fderiv_add hf hg,add_apply,WithLp.equiv_apply,
      WithLp.ofLp_toLp,WithLp.ofLp_add,Pi.add_apply,mul_add]
  map_smul' c f := by
    have hf := sourceKPCompactChartPullback_differentiableAt K hζ f b x hx
    change sourceKPCompactCoreGradientLift K hζ (c • f) b x =
      c • sourceKPCompactCoreGradientLift K hζ f b x
    apply (WithLp.equiv 2 ((InfinitePlace K × Fin 3) → ℂ)).injective
    funext ij
    simp only [sourceKPCompactCoreGradientLift,productPartial,Submodule.coe_smul,
      sourceKPCompactChartPullback_smul,fderiv_const_smul hf,smul_apply,WithLp.equiv_apply,
      WithLp.ofLp_toLp,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul]
    ring

theorem sourceKPCompactCoreGradientLiftLinear_apply (b : SourceKPFiniteLevelFiber K hζ)
    (x : ProductSpace (InfinitePlace K)) (hx : x ∈ productUpper (InfinitePlace K))
    (f : sourceKPCompactC2Core K hζ) :
    sourceKPCompactCoreGradientLiftLinear K hζ b x hx f = sourceKPCompactCoreGradientLift K hζ f b x := rfl

theorem sourceKPCompactCoreGradientLift_norm_sq {n : ℕ∞ω} (f : sourceKPCompactCore K hζ n)
    (b : SourceKPFiniteLevelFiber K hζ) (x : ProductSpace (InfinitePlace K)) :
    ‖sourceKPCompactCoreGradientLift K hζ f b x‖ ^ 2 = sourceKPCompactCoreEnergyLift K hζ f b x := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [sourceKPCompactCoreGradientLift,WithLp.ofLp_toLp,Fintype.sum_prod_type,norm_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,sourceKPCompactCoreEnergyLift,productGradientEnergy,Finset.mul_sum]

def sourceKPCompactCoreGradientAtLinear (y : SourceKPAutomorphicCompactLevel K hζ) :
    sourceKPCompactC2Core K hζ →ₗ[ℂ] H1Vector (InfinitePlace K) :=
  let b := (sourceKPUpperToCompact_cover K hζ y).choose
  let p := (sourceKPUpperToCompact_cover K hζ y).choose_spec.choose
  sourceKPCompactCoreGradientLiftLinear K hζ b (sourceKPArchUpperEuclideanMap K p)
    (fun i _ => sourceArchUpperEuclideanMap_positive (p i))

theorem sourceKPCompactCoreGradientAt_norm_sq (f : sourceKPCompactC2Core K hζ)
    (y : SourceKPAutomorphicCompactLevel K hζ) :
    ‖sourceKPCompactCoreGradientAtLinear K hζ y f‖ ^ 2 = sourceKPCompactCoreEnergy K hζ f y := by
  let b := (sourceKPUpperToCompact_cover K hζ y).choose
  let p := (sourceKPUpperToCompact_cover K hζ y).choose_spec.choose
  change ‖sourceKPCompactCoreGradientLift K hζ f b (sourceKPArchUpperEuclideanMap K p)‖ ^ 2 =
    sourceKPCompactCoreEnergyLift K hζ f b (sourceKPArchUpperEuclideanMap K p)
  exact sourceKPCompactCoreGradientLift_norm_sq K hζ f b (sourceKPArchUpperEuclideanMap K p)

end
end ArtinMatthews
