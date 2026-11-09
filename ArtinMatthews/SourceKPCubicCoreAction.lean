module

public import ArtinMatthews.SourceKPCubicUpperAction
public import ArtinMatthews.SourceKPCompactC2Core
public import ArtinMatthews.SourceKPCompactGenuineL2


set_option backward.privateInPublic true
@[expose] public section

/-! Inverse cubic-center pullback and character averaging preserve the actual scalar core. -/
namespace ArtinMatthews
open NumberField Matrix Topology SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing ContDiff BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] sourceKPCompactCubicCenter_fintype

theorem sourceKPCubicCenter_chartPullback (z : rootsOfUnity 3 K)
    (f : SourceKPAutomorphicCompactLevel K hζ → ℂ) (b : SourceKPFiniteLevelFiber K hζ) :
    sourceKPCompactChartPullback K hζ (fun x => f (z • x)) b =
      sourceKPCompactChartPullback K hζ f (z • b) := by
  funext x
  unfold sourceKPCompactChartPullback
  split_ifs with hx
  · exact congrArg f (sourceKPCubicCenter_upperToCompact K hζ z b
      (sourceKPArchEuclideanUpperMap K x))
  · rfl

theorem sourceKPCubicCenter_core_mem (n : ℕ∞ω) (z : rootsOfUnity 3 K)
    {f : SourceKPAutomorphicCompactLevel K hζ → ℂ} (hf : f ∈ sourceKPCompactCore K hζ n) :
    (fun x => f (z • x)) ∈ sourceKPCompactCore K hζ n := by
  refine ⟨hf.1.comp (sourceKPCubicCenter_compact_continuous K hζ z),
    hf.2.1.comp_homeomorph (sourceKPCubicCenterCompactHomeomorph K hζ z), ?_⟩
  intro b
  rw [sourceKPCubicCenter_chartPullback]
  exact hf.2.2 (z • b)

def sourceKPCubicCorePullback (n : ℕ∞ω) (z : rootsOfUnity 3 K) :
    sourceKPCompactCore K hζ n →ₗ[ℂ] sourceKPCompactCore K hζ n where
  toFun f := ⟨fun x => f.val (z⁻¹ • x), sourceKPCubicCenter_core_mem K hζ n z⁻¹ f.property⟩
  map_add' f g := by
    apply Subtype.ext
    rfl
  map_smul' c f := by
    apply Subtype.ext
    rfl

@[simp] theorem sourceKPCubicCorePullback_apply (n : ℕ∞ω) (z : rootsOfUnity 3 K)
    (f : sourceKPCompactCore K hζ n) (x : SourceKPAutomorphicCompactLevel K hζ) :
    (sourceKPCubicCorePullback K hζ n z f).val x = f.val (z⁻¹ • x) := rfl

def sourceKPCubicCoreRepresentation (n : ℕ∞ω) :
    rootsOfUnity 3 K →* Module.End ℂ (sourceKPCompactCore K hζ n) where
  toFun := sourceKPCubicCorePullback K hζ n
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change f.val ((1 : rootsOfUnity 3 K)⁻¹ • x) = f.val x
    simp only [inv_one, one_smul]
  map_mul' z w := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change f.val ((z * w)⁻¹ • x) = f.val (w⁻¹ • (z⁻¹ • x))
    rw [_root_.mul_inv_rev, mul_smul]

theorem sourceKPCubicCorePullback_chart (n : ℕ∞ω) (z : rootsOfUnity 3 K)
    (f : sourceKPCompactCore K hζ n) (b : SourceKPFiniteLevelFiber K hζ) :
    sourceKPCompactChartPullback K hζ (sourceKPCubicCorePullback K hζ n z f).val b =
      sourceKPCompactChartPullback K hζ f.val (z⁻¹ • b) :=
  sourceKPCubicCenter_chartPullback K hζ z⁻¹ f.val b

theorem sourceKPCubicCorePullback_gradient (n : ℕ∞ω) (z : rootsOfUnity 3 K)
    (f : sourceKPCompactCore K hζ n) (b : SourceKPFiniteLevelFiber K hζ)
    (x : ProductSpace (InfinitePlace K)) :
    sourceKPCompactCoreGradientLift K hζ (sourceKPCubicCorePullback K hζ n z f) b x =
      sourceKPCompactCoreGradientLift K hζ f (z⁻¹ • b) x := by
  unfold sourceKPCompactCoreGradientLift
  rw [sourceKPCubicCorePullback_chart]

theorem sourceKPCubicCorePullback_energy (n : ℕ∞ω) (z : rootsOfUnity 3 K)
    (f : sourceKPCompactCore K hζ n) (b : SourceKPFiniteLevelFiber K hζ)
    (x : ProductSpace (InfinitePlace K)) :
    sourceKPCompactCoreEnergyLift K hζ (sourceKPCubicCorePullback K hζ n z f) b x =
      sourceKPCompactCoreEnergyLift K hζ f (z⁻¹ • b) x := by
  unfold sourceKPCompactCoreEnergyLift
  rw [sourceKPCubicCorePullback_chart]

def sourceKPCubicCoreProjector (n : ℕ∞ω) :
    sourceKPCompactCore K hζ n →ₗ[ℂ] sourceKPCompactCore K hζ n :=
  (3 : ℂ)⁻¹ •
    ∑ z : rootsOfUnity 3 K, (sourceKPAdelicCentralComplex K hζ z : ℂ) •
      sourceKPCubicCorePullback K hζ n z

theorem sourceKPCubicCoreProjector_apply (n : ℕ∞ω) (f : sourceKPCompactCore K hζ n)
    (x : SourceKPAutomorphicCompactLevel K hζ) :
    (sourceKPCubicCoreProjector K hζ n f).val x = (3 : ℂ)⁻¹ *
      ∑ z : rootsOfUnity 3 K, (sourceKPAdelicCentralComplex K hζ z : ℂ) * f.val (z⁻¹ • x) := by
  simp only [sourceKPCubicCoreProjector, LinearMap.smul_apply, LinearMap.sum_apply,
    Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply,
    sourceKPCubicCorePullback_apply, smul_eq_mul]

end
end ArtinMatthews
