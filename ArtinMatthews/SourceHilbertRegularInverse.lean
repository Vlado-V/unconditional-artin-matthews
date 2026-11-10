module

public import ArtinMatthews.SourceHilbertPencil
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Constructions


set_option backward.privateInPublic true
@[expose] public section

/-! The inverse on the orthogonal regular summand is analytic at the
Fredholm center. -/

namespace ArtinMatthews.HilbertResolvent

open Filter
open scoped InnerProductSpace Topology
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def regularGram (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) : regularSpace T center →L[ℂ] regularSpace T center :=
  T.restrict (fun _ hx => preserves_regularSpace T hT center hne hx)

def regularPencil (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (z : ℂ) : regularSpace T center →L[ℂ] regularSpace T center :=
  pencil (regularGram T hT center hne) z

theorem regularPencil_apply (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (z : ℂ) (u : regularSpace T center) :
    (regularPencil T hT center hne z u : E) = pencil T z u := rfl

theorem regularPencil_center_isUnit (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (hF : (pencil T (center : ℂ)).IsFredholm) :
    IsUnit (regularPencil T hT center hne (center : ℂ)) := by
  apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := regularSpace T center)).mpr
  constructor
  · intro u v huv
    have he : pencil T (center : ℂ) u = pencil T (center : ℂ) v :=
      congrArg (fun w : regularSpace T center => (w : E)) huv
    have hn : (u : E) - (v : E) ∈ nullSpace T center := by
      change pencil T (center : ℂ) ((u : E) - (v : E)) = 0
      rw [map_sub, he, sub_self]
    have hr : (u : E) - (v : E) ∈ regularSpace T center :=
      (regularSpace T center).sub_mem u.property v.property
    apply Subtype.ext
    exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp
      ((nullSpace T center).inner_right_of_mem_orthogonal hn hr))
  · intro v
    have hv : (v : E) ∈ (pencil T (center : ℂ)).range := by
      rw [pencil_center_range T hT center hF]
      exact v.property
    obtain ⟨u, hu⟩ := hv
    change pencil T (center : ℂ) u = (v : E) at hu
    refine ⟨⟨u - (nullSpace T center).starProjection u,
      (nullSpace T center).sub_starProjection_mem_orthogonal u⟩, Subtype.ext ?_⟩
    change pencil T (center : ℂ) (u - (nullSpace T center).starProjection u) = (v : E)
    have hn : pencil T (center : ℂ) ((nullSpace T center).starProjection u) = 0 :=
      (nullSpace T center).starProjection_apply_mem u
    rw [map_sub, hu, hn, sub_zero]

theorem pencil_analyticAt (T : E →L[ℂ] E) (z : ℂ) : AnalyticAt ℂ (pencil T) z := by
  have hc := ((ContinuousLinearMap.id ℂ ℂ).smulRight T).analyticAt (z + 1)
  change AnalyticAt ℂ (fun w : ℂ => w • T) (z + 1) at hc
  have hz : AnalyticAt ℂ (fun w : ℂ => w + 1) z := analyticAt_id.add analyticAt_const
  exact analyticAt_const.sub (hc.comp_of_eq hz rfl)

theorem regularPencil_eventually_isUnit (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (hF : (pencil T (center : ℂ)).IsFredholm) :
    ∀ᶠ z : ℂ in 𝓝 (center : ℂ), IsUnit (regularPencil T hT center hne z) :=
  (pencil_analyticAt (regularGram T hT center hne) (center : ℂ)).continuousAt.eventually
    ((Units.isOpen (R := regularSpace T center →L[ℂ] regularSpace T center)).mem_nhds
      (regularPencil_center_isUnit T hT center hne hF))

theorem regularInverse_analyticAt (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (hF : (pencil T (center : ℂ)).IsFredholm) :
    AnalyticAt ℂ (fun z => Ring.inverse (regularPencil T hT center hne z)) (center : ℂ) := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ)
    (A := regularSpace T center →L[ℂ] regularSpace T center))
    (regularPencil T hT center hne (center : ℂ)) (regularPencil_center_isUnit T hT center hne hF)
  exact hi.comp_of_eq (pencil_analyticAt (regularGram T hT center hne) (center : ℂ)) rfl

def regularLift (T : E →L[ℂ] E) (center : ℝ) :
    (regularSpace T center →L[ℂ] regularSpace T center) →L[ℂ] (E →L[ℂ] E) :=
  (ContinuousLinearMap.compL ℂ E (regularSpace T center) E (regularSpace T center).subtypeL).comp
    ((ContinuousLinearMap.compL ℂ E (regularSpace T center) (regularSpace T center)).flip
      (regularSpace T center).orthogonalProjectionOnto)

def regularInverseLift (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (z : ℂ) : E →L[ℂ] E :=
  regularLift T center (Ring.inverse (regularPencil T hT center hne z))

theorem regularInverseLift_analyticAt (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (hF : (pencil T (center : ℂ)).IsFredholm) :
    AnalyticAt ℂ (regularInverseLift T hT center hne) (center : ℂ) := by
  have hl := ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := regularSpace T center →L[ℂ] regularSpace T center) (F := E →L[ℂ] E)
    (regularLift T center) (Ring.inverse (regularPencil T hT center hne (center : ℂ)))
  exact hl.comp_of_eq (regularInverse_analyticAt T hT center hne hF) rfl

theorem pencil_apply_regularInverseLift (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (z : ℂ) (hz : IsUnit (regularPencil T hT center hne z))
    (x : E) :
    pencil T z (regularInverseLift T hT center hne z x) = (regularSpace T center).starProjection x := by
  have he := congrArg (fun A : regularSpace T center →L[ℂ] regularSpace T center =>
    A ((regularSpace T center).orthogonalProjectionOnto x))
    (Ring.mul_inverse_cancel (regularPencil T hT center hne z) hz)
  exact congrArg (fun v : regularSpace T center => (v : E)) he

end
end ArtinMatthews.HilbertResolvent
