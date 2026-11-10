module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Extend


set_option backward.privateInPublic true
@[expose] public section

/-! Compactness passes from a genuine dense core to its bounded extension. -/

noncomputable section
open Set

namespace ArtinMatthews

theorem exists_bounded_extension_of_dense_core {D E F : Type*}
    [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : D →ₗ[ℂ] F) (e : D →ₗ[ℂ] E) (he : DenseRange e)
    (hb : ∃ C : ℝ, ∀ d, ‖f d‖ ≤ C * ‖e d‖) :
    ∃ A : E →L[ℂ] F, ∀ d, A (e d) = f d :=
  ⟨f.extendOfNorm e,LinearMap.extendOfNorm_eq he hb⟩

/-- Function-level interface avoids imposing a chosen additive-instance path
on a concrete dense algebraic core. Linearity is checked explicitly. -/
theorem exists_bounded_extension_of_dense_functions {D E F : Type*}
    [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : D → F) (e : D → E) (he : DenseRange e)
    (hfadd : ∀ x y, f (x+y) = f x+f y) (hfsmul : ∀ (c : ℂ) x, f (c • x) = c • f x)
    (headd : ∀ x y, e (x+y) = e x+e y) (hesmul : ∀ (c : ℂ) x, e (c • x) = c • e x)
    (hb : ∃ C : ℝ, ∀ d, ‖f d‖ ≤ C * ‖e d‖) :
    ∃ A : E →L[ℂ] F, ∀ d, A (e d) = f d := by
  let fl : D →ₗ[ℂ] F := { toFun := f, map_add' := hfadd, map_smul' := hfsmul }
  let el : D →ₗ[ℂ] E := { toFun := e, map_add' := headd, map_smul' := hesmul }
  exact exists_bounded_extension_of_dense_core fl el he hb

theorem compactOperator_of_dense_core {D E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : D → E) (he : DenseRange e) (A : E →L[ℂ] F)
    (hcompact : IsCompact (closure (range (fun d : {d : D // ‖e d‖ ≤ 2} => A (e d))))) :
    IsCompactOperator A := by
  apply (isCompactOperator_iff_image_ball_subset_compact A.toLinearMap
    (by norm_num : (0 : ℝ) < 1)).mpr
  refine ⟨_,hcompact,?_⟩
  rintro _ ⟨u,hu,rfl⟩
  have hc : u ∈ closure (Metric.ball (0 : E) 1 ∩ range e) :=
    (show Dense (range e) from he).open_subset_closure_inter Metric.isOpen_ball hu
  apply closure_mono ?_ (mem_closure_image A.continuous.continuousAt hc)
  rintro _ ⟨v,⟨hv,⟨d,rfl⟩⟩,rfl⟩
  have hd : ‖e d‖ ≤ 2 := by
    have hlt : ‖e d‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hv
    linarith
  exact ⟨⟨d,hd⟩,rfl⟩

end ArtinMatthews
