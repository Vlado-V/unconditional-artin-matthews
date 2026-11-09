module

public import ArtinMatthews.SourceKPFiniteChartCoordinates
public import ArtinMatthews.SourceKPArchTestPullback


set_option backward.privateInPublic true
@[expose] public section

/-! Finite averaging on the exact finite-cover stabilizer, with the original scalar L2 space. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

abbrev SourceKPFiniteChartTests := h1LocalTests (sourceKPFiniteChartCoordinateDomain K hζ b p)
abbrev SourceKPFiniteChartMass := h1SupportedMass (sourceKPFiniteChartCoordinateDomain K hζ b p)

instance sourceKPFiniteChartMass_complete : CompleteSpace (SourceKPFiniteChartMass K hζ b p) :=
  (h1SupportedMass_isClosed _ (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p).measurableSet).completeSpace_coe

def sourceKPFiniteChartTestPullback (γ : SourceKPFiniteChartStabilizer K hζ b p) :
    SourceKPFiniteChartTests K hζ b p →ₗ[ℂ] SourceKPFiniteChartTests K hζ b p :=
  ((sourceKPArchTestPullbackLinear K hζ γ.val.val).comp
    (h1LocalTests (sourceKPFiniteChartCoordinateDomain K hζ b p)).subtype).codRestrict _ (by
      intro f x hx
      obtain ⟨y,hy,rfl⟩ := sourceKPArchTestPullbackFun_tsupport K hζ γ.val.val f.val hx
      exact sourceKPFiniteChartCoordinateDomain_invariant K hζ b p γ⁻¹ (f.prop hy))

theorem sourceKPFiniteChartMass_pullback_mem (γ : SourceKPFiniteChartStabilizer K hζ b p)
    (f : SourceKPFiniteChartMass K hζ b p) :
    sourceKPArchL2Pullback K hζ γ.val.val f.val ∈ SourceKPFiniteChartMass K hζ b p := by
  let U := sourceKPFiniteChartCoordinateDomain K hζ b p
  have hd : DenseRange (h1LocalTestMass U) := h1LocalTestMass_denseRange U
    (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p)
    (sourceKPFiniteChartCoordinateDomain_upper K hζ b p)
  refine hd.induction_on
    (p := fun t : h1SupportedMass U => sourceKPArchL2Pullback K hζ γ.val.val t.val ∈ h1SupportedMass U)
    f ?_ ?_
  · exact (h1SupportedMass_isClosed U (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p).measurableSet).preimage
      ((sourceKPArchL2Pullback K hζ γ.val.val).continuous.comp continuous_subtype_val)
  · intro g
    change sourceKPArchL2Pullback K hζ γ.val.val (h1TestMass g.val) ∈ _
    rw [← sourceKPArchL2Pullback_core]
    exact (h1LocalTestMass U (sourceKPFiniteChartTestPullback K hζ b p γ g)).prop

def sourceKPFiniteChartMassPullback (γ : SourceKPFiniteChartStabilizer K hζ b p) :
    SourceKPFiniteChartMass K hζ b p →L[ℂ] SourceKPFiniteChartMass K hζ b p :=
  ((sourceKPArchL2Pullback K hζ γ.val.val).toContinuousLinearMap.comp
    (h1SupportedMass (sourceKPFiniteChartCoordinateDomain K hζ b p)).subtypeL).codRestrict _
      (sourceKPFiniteChartMass_pullback_mem K hζ b p γ)

theorem sourceKPFiniteChartMassPullback_mul (γ δ : SourceKPFiniteChartStabilizer K hζ b p)
    (f : SourceKPFiniteChartMass K hζ b p) :
    sourceKPFiniteChartMassPullback K hζ b p γ (sourceKPFiniteChartMassPullback K hζ b p δ f) =
      sourceKPFiniteChartMassPullback K hζ b p (δ*γ) f := by
  apply Subtype.ext
  exact sourceKPArchL2Pullback_mul K hζ γ.val.val δ.val.val f.val

def sourceKPFiniteChartInvariantMass : Submodule ℂ (SourceKPFiniteChartMass K hζ b p) where
  carrier := {f | ∀ γ : SourceKPFiniteChartStabilizer K hζ b p,
    sourceKPFiniteChartMassPullback K hζ b p γ f = f}
  zero_mem' := by intro γ; exact map_zero _
  add_mem' := by
    intro f g hf hg γ
    rw [map_add,hf γ,hg γ]
  smul_mem' := by
    intro c f hf γ
    rw [map_smul,hf γ]

theorem sourceKPFiniteChartInvariantMass_isClosed :
    IsClosed (sourceKPFiniteChartInvariantMass K hζ b p : Set (SourceKPFiniteChartMass K hζ b p)) := by
  change IsClosed {f | ∀ γ : SourceKPFiniteChartStabilizer K hζ b p,
    sourceKPFiniteChartMassPullback K hζ b p γ f = f}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun γ => isClosed_eq (sourceKPFiniteChartMassPullback K hζ b p γ).continuous continuous_id

instance sourceKPFiniteChartInvariantMass_complete :
    CompleteSpace (sourceKPFiniteChartInvariantMass K hζ b p) :=
  (sourceKPFiniteChartInvariantMass_isClosed K hζ b p).completeSpace_coe

def sourceKPFiniteChartMassAverage :
    SourceKPFiniteChartMass K hζ b p →L[ℂ] SourceKPFiniteChartMass K hζ b p :=
  (Fintype.card (SourceKPFiniteChartStabilizer K hζ b p) : ℂ)⁻¹ •
    ∑ γ : SourceKPFiniteChartStabilizer K hζ b p, sourceKPFiniteChartMassPullback K hζ b p γ

def sourceKPFiniteChartTestAverage :
    SourceKPFiniteChartTests K hζ b p →ₗ[ℂ] SourceKPFiniteChartTests K hζ b p :=
  (Fintype.card (SourceKPFiniteChartStabilizer K hζ b p) : ℂ)⁻¹ •
    ∑ γ : SourceKPFiniteChartStabilizer K hζ b p, sourceKPFiniteChartTestPullback K hζ b p γ

theorem sourceKPFiniteChartTestPullback_apply (γ : SourceKPFiniteChartStabilizer K hζ b p)
    (f : SourceKPFiniteChartTests K hζ b p) (x : ProductSpace (InfinitePlace K))
    (hx : x ∈ productUpper (InfinitePlace K)) :
    (sourceKPFiniteChartTestPullback K hζ b p γ f).val.val x =
      f.val.val (sourceKPArchEuclideanAction K hζ γ.val.val x) := by
  change (if x ∈ productUpper (InfinitePlace K) then
    f.val.val (sourceKPArchEuclideanAction K hζ γ.val.val x) else 0) = _
  exact ite_eq_left hx

theorem sourceKPFiniteChartTestAverage_apply (f : SourceKPFiniteChartTests K hζ b p)
    (x : ProductSpace (InfinitePlace K)) (hx : x ∈ productUpper (InfinitePlace K)) :
    (sourceKPFiniteChartTestAverage K hζ b p f).val.val x =
      (Fintype.card (SourceKPFiniteChartStabilizer K hζ b p) : ℂ)⁻¹ •
        ∑ γ : SourceKPFiniteChartStabilizer K hζ b p,
          f.val.val (sourceKPArchEuclideanAction K hζ γ.val.val x) := by
  simp only [sourceKPFiniteChartTestAverage,LinearMap.smul_apply,LinearMap.sum_apply,
    Submodule.coe_smul,Submodule.coe_sum,Pi.smul_apply,Finset.sum_apply,
    sourceKPFiniteChartTestPullback_apply K hζ b p _ f x hx]

theorem sourceKPFiniteChartTestAverage_invariant (f : SourceKPFiniteChartTests K hζ b p)
    (δ : SourceKPFiniteChartStabilizer K hζ b p) (x : ProductSpace (InfinitePlace K))
    (hx : x ∈ productUpper (InfinitePlace K)) :
    (sourceKPFiniteChartTestAverage K hζ b p f).val.val
      (sourceKPArchEuclideanAction K hζ δ.val.val x) =
      (sourceKPFiniteChartTestAverage K hζ b p f).val.val x := by
  rw [sourceKPFiniteChartTestAverage_apply K hζ b p f _
    (sourceKPArchEuclideanAction_positive K hζ δ.val.val x),
    sourceKPFiniteChartTestAverage_apply K hζ b p f x hx]
  apply congrArg ((Fintype.card (SourceKPFiniteChartStabilizer K hζ b p) : ℂ)⁻¹ • ·)
  simp_rw [← sourceKPArchEuclideanAction_mul]
  simpa only [Equiv.coe_mulRight,Subgroup.coe_mul] using
    Equiv.sum_comp (Equiv.mulRight δ)
      (fun γ : SourceKPFiniteChartStabilizer K hζ b p =>
        f.val.val (sourceKPArchEuclideanAction K hζ γ.val.val x))

theorem sourceKPFiniteChartMassAverage_invariant (f : SourceKPFiniteChartMass K hζ b p) :
    sourceKPFiniteChartMassAverage K hζ b p f ∈ sourceKPFiniteChartInvariantMass K hζ b p := by
  intro δ
  simp only [sourceKPFiniteChartMassAverage,smul_apply,
    sum_apply]
  rw [map_smul,map_sum]
  apply congrArg ((Fintype.card (SourceKPFiniteChartStabilizer K hζ b p) : ℂ)⁻¹ • ·)
  simp_rw [sourceKPFiniteChartMassPullback_mul]
  exact Equiv.sum_comp (Equiv.mulRight δ) (fun γ => sourceKPFiniteChartMassPullback K hζ b p γ f)

theorem sourceKPFiniteChartMassAverage_fixed (f : sourceKPFiniteChartInvariantMass K hζ b p) :
    sourceKPFiniteChartMassAverage K hζ b p f.val = f.val := by
  have hf : ∀ γ : SourceKPFiniteChartStabilizer K hζ b p,
      sourceKPFiniteChartMassPullback K hζ b p γ f.val = f.val := f.prop
  simp only [sourceKPFiniteChartMassAverage,smul_apply,sum_apply]
  simp_rw [hf]
  rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℂ,smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),one_smul]

theorem sourceKPFiniteChartAverage_core (f : SourceKPFiniteChartTests K hζ b p) :
    h1LocalTestMass _ (sourceKPFiniteChartTestAverage K hζ b p f) =
      sourceKPFiniteChartMassAverage K hζ b p (h1LocalTestMass _ f) := by
  simp only [sourceKPFiniteChartTestAverage,sourceKPFiniteChartMassAverage,
    LinearMap.smul_apply,LinearMap.sum_apply,smul_apply,sum_apply,map_smul,map_sum]
  apply congrArg ((Fintype.card (SourceKPFiniteChartStabilizer K hζ b p) : ℂ)⁻¹ • ·)
  apply Finset.sum_congr rfl
  intro γ _
  apply Subtype.ext
  exact sourceKPArchL2Pullback_core K hζ γ.val.val f.val

end
end ArtinMatthews
