module

public import ArtinMatthews.SourceKPArchActionSmooth
public import ArtinMatthews.SourceHyperbolicH1LocalTests


set_option backward.privateInPublic true
@[expose] public section

/-! Actual projective pullback preserves the compact chart test class. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen Filter
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPArchTestPullbackFun (a : PGL(2, InfiniteAdeleRing K))
    (f : h1Tests (InfinitePlace K) 2) (p : ProductSpace (InfinitePlace K)) : ℂ :=
  if p ∈ productUpper (InfinitePlace K) then f.val (sourceKPArchEuclideanAction K hζ a p) else 0

theorem sourceKPArchTestPullbackFun_support (a : PGL(2, InfiniteAdeleRing K))
    (f : h1Tests (InfinitePlace K) 2) :
    Function.support (sourceKPArchTestPullbackFun K hζ a f) ⊆
      sourceKPArchEuclideanAction K hζ a⁻¹ '' tsupport f.val := by
  intro p hp
  by_cases hu : p ∈ productUpper (InfinitePlace K)
  · have hf : f.val (sourceKPArchEuclideanAction K hζ a p) ≠ 0 := by
      simpa only [sourceKPArchTestPullbackFun,ite_eq_left hu,Function.mem_support] using hp
    refine ⟨sourceKPArchEuclideanAction K hζ a p,subset_tsupport f.val hf,?_⟩
    rw [← sourceKPArchEuclideanAction_mul,inv_mul_cancel,sourceKPArchEuclideanAction_one K hζ p hu]
  · exact False.elim (hp (by simp only [sourceKPArchTestPullbackFun,ite_eq_right hu]))

theorem sourceKPArchTestPullbackFun_compactImage (a : PGL(2, InfiniteAdeleRing K))
    (f : h1Tests (InfinitePlace K) 2) :
    IsCompact (sourceKPArchEuclideanAction K hζ a⁻¹ '' tsupport f.val) := by
  apply f.prop.2.1.image_of_continuousOn
  intro p hp
  exact (sourceKPArchEuclideanAction_contDiffAt K hζ a⁻¹ p (f.prop.2.2 hp)).continuousAt.continuousWithinAt

theorem sourceKPArchTestPullbackFun_tsupport (a : PGL(2, InfiniteAdeleRing K))
    (f : h1Tests (InfinitePlace K) 2) :
    tsupport (sourceKPArchTestPullbackFun K hζ a f) ⊆
      sourceKPArchEuclideanAction K hζ a⁻¹ '' tsupport f.val :=
  closure_minimal (sourceKPArchTestPullbackFun_support K hζ a f)
    (sourceKPArchTestPullbackFun_compactImage K hζ a f).isClosed

theorem sourceKPArchTestPullbackFun_tsupport_upper (a : PGL(2, InfiniteAdeleRing K))
    (f : h1Tests (InfinitePlace K) 2) :
    tsupport (sourceKPArchTestPullbackFun K hζ a f) ⊆ productUpper (InfinitePlace K) := by
  intro p hp
  obtain ⟨x,_hx,rfl⟩ := sourceKPArchTestPullbackFun_tsupport K hζ a f hp
  exact sourceKPArchEuclideanAction_positive K hζ a⁻¹ x

theorem sourceKPArchTestPullbackFun_contDiff (a : PGL(2, InfiniteAdeleRing K))
    (f : h1Tests (InfinitePlace K) 2) :
    ContDiff ℝ 2 (sourceKPArchTestPullbackFun K hζ a f) := by
  apply product_test_contDiff_of_contDiffOn _ (sourceKPArchTestPullbackFun_tsupport_upper K hζ a f)
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have hcomp := f.prop.1.contDiffAt.comp p
    ((sourceKPArchEuclideanAction_contDiffAt K hζ a p hp).of_le (by simp))
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(productUpper_isOpen (InfinitePlace K)).mem_nhds hp] with q hq
  simp only [sourceKPArchTestPullbackFun,ite_eq_left hq,Function.comp_apply]

def sourceKPArchTestPullback (a : PGL(2, InfiniteAdeleRing K))
    (f : h1Tests (InfinitePlace K) 2) : h1Tests (InfinitePlace K) 2 :=
  ⟨sourceKPArchTestPullbackFun K hζ a f,sourceKPArchTestPullbackFun_contDiff K hζ a f,
    (sourceKPArchTestPullbackFun_compactImage K hζ a f).of_isClosed_subset isClosed_closure
      (sourceKPArchTestPullbackFun_tsupport K hζ a f),
    sourceKPArchTestPullbackFun_tsupport_upper K hζ a f⟩

def sourceKPArchL2Pullback (a : PGL(2, InfiniteAdeleRing K)) :
    H1Mass (InfinitePlace K) →ₗᵢ[ℂ] H1Mass (InfinitePlace K) :=
  Lp.compMeasurePreservingₗᵢ ℂ (sourceKPArchEuclideanAction K hζ a)
    (sourceKPArchEuclideanAction_preserving K hζ a)

def sourceKPArchTestPullbackLinear (a : PGL(2, InfiniteAdeleRing K)) :
    h1Tests (InfinitePlace K) 2 →ₗ[ℂ] h1Tests (InfinitePlace K) 2 where
  toFun := sourceKPArchTestPullback K hζ a
  map_add' f g := by
    apply Subtype.ext
    funext p
    change (if p ∈ productUpper (InfinitePlace K) then
      f.val (sourceKPArchEuclideanAction K hζ a p) + g.val (sourceKPArchEuclideanAction K hζ a p) else 0) = _
    by_cases hp : p ∈ productUpper (InfinitePlace K) <;>
      simp only [hp,ite_true,ite_false,sourceKPArchTestPullback,sourceKPArchTestPullbackFun,
        Submodule.coe_add,Pi.add_apply,add_zero]
  map_smul' c f := by
    apply Subtype.ext
    funext p
    change (if p ∈ productUpper (InfinitePlace K) then
      c • f.val (sourceKPArchEuclideanAction K hζ a p) else 0) = _
    by_cases hp : p ∈ productUpper (InfinitePlace K) <;>
      simp only [hp,ite_true,ite_false,sourceKPArchTestPullback,sourceKPArchTestPullbackFun,
        Submodule.coe_smul,Pi.smul_apply,smul_zero,RingHom.id_apply]

theorem sourceKPArchL2Pullback_mul (a b : PGL(2, InfiniteAdeleRing K))
    (f : H1Mass (InfinitePlace K)) :
    sourceKPArchL2Pullback K hζ a (sourceKPArchL2Pullback K hζ b f) =
      sourceKPArchL2Pullback K hζ (b*a) f := by
  change Lp.compMeasurePreserving (sourceKPArchEuclideanAction K hζ a) _
      (Lp.compMeasurePreserving (sourceKPArchEuclideanAction K hζ b) _ f) =
    Lp.compMeasurePreserving (sourceKPArchEuclideanAction K hζ (b*a)) _ f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : sourceKPArchEuclideanAction K hζ b ∘ sourceKPArchEuclideanAction K hζ a =
      sourceKPArchEuclideanAction K hζ (b*a) := by
    funext p
    exact (sourceKPArchEuclideanAction_mul K hζ b a p).symm
  simp only [he]

theorem sourceKPArchL2Pullback_one (f : H1Mass (InfinitePlace K)) :
    sourceKPArchL2Pullback K hζ 1 f = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (sourceKPArchEuclideanAction_preserving K hζ 1),
    productVolume_ae_upper (ι := InfinitePlace K)] with p hp hu
  exact hp.trans (congrArg f (sourceKPArchEuclideanAction_one K hζ p hu))

theorem sourceKPArchL2Pullback_core (a : PGL(2, InfiniteAdeleRing K))
    (f : h1Tests (InfinitePlace K) 2) :
    h1TestMass (sourceKPArchTestPullback K hζ a f) = sourceKPArchL2Pullback K hζ a (h1TestMass f) := by
  apply Lp.ext
  have hcomp := (sourceKPArchEuclideanAction_preserving K hζ a).quasiMeasurePreserving.ae (h1TestMass_coe f)
  filter_upwards [h1TestMass_coe (sourceKPArchTestPullback K hζ a f),
    Lp.coeFn_compMeasurePreserving (h1TestMass f) (sourceKPArchEuclideanAction_preserving K hζ a),
    hcomp,productVolume_ae_upper (ι := InfinitePlace K)] with p hp hq hf hu
  rw [hp]
  change (sourceKPArchTestPullback K hζ a f : ProductSpace (InfinitePlace K) → ℂ) p =
    (Lp.compMeasurePreserving (sourceKPArchEuclideanAction K hζ a)
      (sourceKPArchEuclideanAction_preserving K hζ a) (h1TestMass f)) p
  rw [hq]
  change (if p ∈ productUpper (InfinitePlace K) then
    f.val (sourceKPArchEuclideanAction K hζ a p) else 0) =
      (h1TestMass f) (sourceKPArchEuclideanAction K hζ a p)
  rw [hf,ite_eq_left hu]

end
end ArtinMatthews
