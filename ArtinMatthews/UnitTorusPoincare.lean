module

public import ArtinMatthews.UnitTorusSobolevClosure


set_option backward.privateInPublic true
@[expose] public section

/-! The standard torus Poincare inequality for actual coordinate derivatives and their H1 closure. -/
namespace ArtinMatthews
open MeasureTheory UnitAddTorus
open scoped BigOperators Topology ENNReal
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem unitTorus_coordinate_poincare
    (f : C(UnitAddTorus ι, ℂ)) (g : ι → C(UnitAddTorus ι, ℂ))
    (hd : ∀ (j : ι) (x : UnitAddTorus ι) (t : ℝ),
      HasDerivAt (fun u : ℝ => f (Function.update x j (u : UnitAddCircle)))
        (g j (Function.update x j (t : UnitAddCircle))) t)
    (hmean : (∫ x, f x ∂unitTorusHaar ι) = 0) :
    (2 * Real.pi) ^ 2 * (∫ x, ‖f x‖ ^ 2 ∂unitTorusHaar ι) ≤
      ∑ j, ∫ x, ‖g j x‖ ^ 2 ∂unitTorusHaar ι := by
  have hf := ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) (unitTorusHaar ι) f
  have hg (j : ι) := ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) (unitTorusHaar ι) (g j)
  have hm : (∫ x, (f.toLp 2 (unitTorusHaar ι) ℂ) x ∂unitTorusHaar ι) = 0 :=
    (integral_congr_ae hf).trans hmean
  have hfnorm : (∫ x, ‖(f.toLp 2 (unitTorusHaar ι) ℂ) x‖ ^ 2 ∂unitTorusHaar ι) =
      ∫ x, ‖f x‖ ^ 2 ∂unitTorusHaar ι := integral_congr_ae (hf.fun_comp fun z : ℂ => ‖z‖ ^ 2)
  have hgnorm (j : ι) : (∫ x, ‖((g j).toLp 2 (unitTorusHaar ι) ℂ) x‖ ^ 2 ∂unitTorusHaar ι) =
      ∫ x, ‖g j x‖ ^ 2 ∂unitTorusHaar ι := integral_congr_ae ((hg j).fun_comp fun z : ℂ => ‖z‖ ^ 2)
  simpa only [hfnorm, hgnorm] using unitTorusWeakGradient_poincare ι _ _
    (unitTorusWeakGradient_of_coordinate_derivative ι f g hd) hm

omit [DecidableEq ι] in
theorem unitTorusMeanZeroGradient_isClosed :
    IsClosed {fg : UnitTorusL2 ι × (ι → UnitTorusL2 ι) |
      UnitTorusWeakGradient ι fg.1 fg.2 ∧ (∫ x, fg.1 x ∂unitTorusHaar ι) = 0} := by
  have heq : {fg : UnitTorusL2 ι × (ι → UnitTorusL2 ι) |
      UnitTorusWeakGradient ι fg.1 fg.2 ∧ (∫ x, fg.1 x ∂unitTorusHaar ι) = 0} =
      {fg | UnitTorusWeakGradient ι fg.1 fg.2} ∩
        {fg | unitTorusCoefficient ι (0 : ι → ℤ) fg.1 = 0} := by
    ext fg
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, unitTorusCoefficient_apply, unitTorus_fourier_zero]
  rw [heq]
  exact (unitTorusWeakGradient_isClosed ι).inter
    (isClosed_eq ((unitTorusCoefficient ι (0 : ι → ℤ)).continuous.comp continuous_fst) continuous_const)

theorem unitTorus_poincare_of_l2_limits {κ : Type*} {l : Filter κ} [Filter.NeBot l]
    (f : κ → C(UnitAddTorus ι, ℂ)) (g : κ → ι → C(UnitAddTorus ι, ℂ))
    (hd : ∀ k (j : ι) (x : UnitAddTorus ι) (t : ℝ),
      HasDerivAt (fun u : ℝ => f k (Function.update x j (u : UnitAddCircle)))
        (g k j (Function.update x j (t : UnitAddCircle))) t)
    (hmean : ∀ k, (∫ x, f k x ∂unitTorusHaar ι) = 0)
    (F : UnitTorusL2 ι) (G : ι → UnitTorusL2 ι)
    (hf : Filter.Tendsto (fun k => (f k).toLp 2 (unitTorusHaar ι) ℂ) l (𝓝 F))
    (hg : Filter.Tendsto (fun k j => (g k j).toLp 2 (unitTorusHaar ι) ℂ) l (𝓝 G)) :
    (2 * Real.pi) ^ 2 * (∫ x, ‖F x‖ ^ 2 ∂unitTorusHaar ι) ≤
      ∑ j, ∫ x, ‖G j x‖ ^ 2 ∂unitTorusHaar ι := by
  have hmem : ∀ᶠ k in l,
      UnitTorusWeakGradient ι ((f k).toLp 2 (unitTorusHaar ι) ℂ)
        (fun j => (g k j).toLp 2 (unitTorusHaar ι) ℂ) ∧
      (∫ x, ((f k).toLp 2 (unitTorusHaar ι) ℂ) x ∂unitTorusHaar ι) = 0 := by
    apply Filter.Eventually.of_forall
    intro k
    refine ⟨unitTorusWeakGradient_of_coordinate_derivative ι (f k) (g k) (hd k), ?_⟩
    exact (integral_congr_ae (ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ)
      (unitTorusHaar ι) (f k))).trans (hmean k)
  have hclosed := (unitTorusMeanZeroGradient_isClosed ι).mem_of_tendsto (hf.prodMk_nhds hg) hmem
  exact unitTorusWeakGradient_poincare ι F G hclosed.1 hclosed.2

end
end ArtinMatthews
