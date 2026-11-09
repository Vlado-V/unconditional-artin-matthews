module

public import ArtinMatthews.SourceHilbertRegularInverse
public import Mathlib.Analysis.Meromorphic.Order


set_option backward.privateInPublic true
@[expose] public section

/-! The exact finite-rank singular term of a self-adjoint Fredholm pencil.
The same formula includes the removable case when the kernel is zero. -/

namespace ArtinMatthews.HilbertResolvent

open Filter
open scoped InnerProductSpace Topology
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def poleResidue (T : E →L[ℂ] E) (center : ℝ) : E →L[ℂ] E :=
  (-((center : ℂ) + 1)) • (nullSpace T center).starProjection

theorem poleResidue_range (T : E →L[ℂ] E) (center : ℝ) (hne : center + 1 ≠ 0) :
    (poleResidue T center).range = nullSpace T center := by
  let c : ℂ := -((center : ℂ) + 1)
  have hc : c ≠ 0 := neg_ne_zero.mpr (centerScalar_ne_zero hne)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (nullSpace T center).smul_mem c ((nullSpace T center).starProjection_apply_mem y)
  · intro hx
    refine ⟨c⁻¹ • x, ?_⟩
    change c • (nullSpace T center).starProjection (c⁻¹ • x) = x
    rw [map_smul, (nullSpace T center).starProjection_eq_self_iff.mpr hx,
      smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem poleResidue_finiteDimensional (T : E →L[ℂ] E) (center : ℝ)
    (hne : center + 1 ≠ 0) (hF : (pencil T (center : ℂ)).IsFredholm) :
    FiniteDimensional ℂ (poleResidue T center).range := by
  rw [poleResidue_range T center hne]
  exact nullSpace_finiteDimensional T center hF

theorem poleResidue_ne_zero_iff (T : E →L[ℂ] E) (center : ℝ) (hne : center + 1 ≠ 0) :
    poleResidue T center ≠ 0 ↔ nullSpace T center ≠ ⊥ := by
  rw [← poleResidue_range T center hne]
  have hr : (poleResidue T center).range = ⊥ ↔ poleResidue T center = 0 := by
    rw [LinearMap.range_eq_bot, ← ContinuousLinearMap.toLinearMap_zero,
      ContinuousLinearMap.coe_inj]
  exact not_congr hr.symm

def localInverse (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (z : ℂ) : E →L[ℂ] E :=
  ((-((center : ℂ) + 1)) / (z - (center : ℂ))) • (nullSpace T center).starProjection +
    regularInverseLift T hT center hne z

theorem localInverse_right_inverse (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (z : ℂ) (hz : z ≠ (center : ℂ))
    (hR : IsUnit (regularPencil T hT center hne z)) (x : E) :
    pencil T z (localInverse T hT center hne z x) = x := by
  change pencil T z
    (((-((center : ℂ) + 1)) / (z - (center : ℂ))) • (nullSpace T center).starProjection x +
      regularInverseLift T hT center hne z x) = x
  rw [map_add, map_smul, pencil_apply_of_mem_null T center hne z
    ((nullSpace T center).starProjection_apply_mem x), smul_smul,
    pencil_apply_regularInverseLift T hT center hne z hR]
  have hc : ((-((center : ℂ) + 1)) / (z - (center : ℂ))) *
      (((center : ℂ) - z) / ((center : ℂ) + 1)) = 1 := by
    field_simp [sub_ne_zero.mpr hz, centerScalar_ne_zero hne] <;> ring
  rw [hc, one_smul]
  exact (nullSpace T center).starProjection_add_starProjection_orthogonal x

theorem pencil_normal (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (z : ℂ) :
    IsStarNormal (pencil T z) := by
  letI : IsStarNormal T := hT.isStarNormal
  unfold pencil
  infer_instance

theorem pencil_isUnit_of_regular (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (z : ℂ) (hz : z ≠ (center : ℂ))
    (hR : IsUnit (regularPencil T hT center hne z)) : IsUnit (pencil T z) := by
  have hsur : Function.Surjective (pencil T z) := fun x =>
    ⟨localInverse T hT center hne z x, localInverse_right_inverse T hT center hne z hz hR x⟩
  apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := E)).mpr
  refine ⟨?_, hsur⟩
  change Function.Injective (pencil T z).toLinearMap
  apply LinearMap.ker_eq_bot.mp
  rw [← ContinuousLinearMap.IsStarNormal.orthogonal_range (pencil_normal T hT z)]
  have hr : (pencil T z).range = ⊤ := LinearMap.range_eq_top.mpr hsur
  rw [hr, Submodule.top_orthogonal_eq_bot]

theorem inverse_eq_localInverse (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (z : ℂ) (hz : z ≠ (center : ℂ))
    (hR : IsUnit (regularPencil T hT center hne z)) :
    Ring.inverse (pencil T z) = localInverse T hT center hne z := by
  have hu := pencil_isUnit_of_regular T hT center hne z hz hR
  apply ContinuousLinearMap.ext
  intro x
  apply ((ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := E)).mp hu).1
  rw [localInverse_right_inverse T hT center hne z hz hR]
  exact congrArg (fun A : E →L[ℂ] E => A x) (Ring.mul_inverse_cancel (pencil T z) hu)

theorem eventually_isUnit_and_inverse_eq (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (hF : (pencil T (center : ℂ)).IsFredholm) :
    ∀ᶠ z : ℂ in 𝓝[≠] (center : ℂ),
      IsUnit (pencil T z) ∧ Ring.inverse (pencil T z) = localInverse T hT center hne z := by
  filter_upwards [(regularPencil_eventually_isUnit T hT center hne hF).filter_mono
    nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hR hz
  exact ⟨pencil_isUnit_of_regular T hT center hne z hz hR,
    inverse_eq_localInverse T hT center hne z hz hR⟩

theorem eventually_inverse_eq (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (hF : (pencil T (center : ℂ)).IsFredholm) :
    (fun z => Ring.inverse (pencil T z)) =ᶠ[𝓝[≠] (center : ℂ)] localInverse T hT center hne :=
  (eventually_isUnit_and_inverse_eq T hT center hne hF).mono (fun _ h => h.2)

theorem inverse_meromorphicAt (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (hF : (pencil T (center : ℂ)).IsFredholm) :
    MeromorphicAt (fun z => Ring.inverse (pencil T z)) (center : ℂ) := by
  have hc : MeromorphicAt (fun z : ℂ => (-((center : ℂ) + 1)) / (z - (center : ℂ)))
      (center : ℂ) := by fun_prop
  have hl : MeromorphicAt (localInverse T hT center hne) (center : ℂ) :=
    (hc.smul (MeromorphicAt.const (nullSpace T center).starProjection (center : ℂ))).add
      (regularInverseLift_analyticAt T hT center hne hF).meromorphicAt
  exact hl.congr (eventually_inverse_eq T hT center hne hF).symm

def desingularizedInverse (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (z : ℂ) : E →L[ℂ] E :=
  poleResidue T center + (z - (center : ℂ)) • regularInverseLift T hT center hne z

theorem desingularizedInverse_center (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) :
    desingularizedInverse T hT center hne (center : ℂ) = poleResidue T center := by
  simp [desingularizedInverse]

theorem desingularizedInverse_analyticAt (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (hF : (pencil T (center : ℂ)).IsFredholm) :
    AnalyticAt ℂ (desingularizedInverse T hT center hne) (center : ℂ) := by
  have hz : AnalyticAt ℂ (fun z : ℂ => z - (center : ℂ)) (center : ℂ) :=
    analyticAt_id.sub analyticAt_const
  exact analyticAt_const.add (hz.smul (regularInverseLift_analyticAt T hT center hne hF))

theorem eventually_desingularizedInverse_eq (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (hF : (pencil T (center : ℂ)).IsFredholm) :
    desingularizedInverse T hT center hne =ᶠ[𝓝[≠] (center : ℂ)]
      (fun z => (z - (center : ℂ)) • Ring.inverse (pencil T z)) := by
  filter_upwards [eventually_inverse_eq T hT center hne hF, self_mem_nhdsWithin] with z h hz
  have hc : (z - (center : ℂ)) * ((-((center : ℂ) + 1)) / (z - (center : ℂ))) =
      -((center : ℂ) + 1) := by
    rw [mul_comm, div_mul_cancel₀ _ (sub_ne_zero.mpr (show z ≠ (center : ℂ) from hz))]
  change desingularizedInverse T hT center hne z = (z - (center : ℂ)) • Ring.inverse (pencil T z)
  rw [h, localInverse, smul_add, smul_smul, hc]
  rfl

theorem inverse_residue_tendsto (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (hF : (pencil T (center : ℂ)).IsFredholm) :
    Tendsto (fun z => (z - (center : ℂ)) • Ring.inverse (pencil T z))
      (𝓝[≠] (center : ℂ)) (𝓝 (poleResidue T center)) := by
  have hc : Tendsto (desingularizedInverse T hT center hne) (𝓝 (center : ℂ))
      (𝓝 (desingularizedInverse T hT center hne (center : ℂ))) :=
    (desingularizedInverse_analyticAt T hT center hne hF).continuousAt
  rw [desingularizedInverse_center] at hc
  exact (hc.mono_left nhdsWithin_le_nhds).congr'
    (eventually_desingularizedInverse_eq T hT center hne hF)

theorem inverse_order_neg_one (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) (hF : (pencil T (center : ℂ)).IsFredholm)
    (hN : nullSpace T center ≠ ⊥) :
    meromorphicOrderAt (fun z => Ring.inverse (pencil T z)) (center : ℂ) =
      ((-1 : ℤ) : WithTop ℤ) := by
  apply (meromorphicOrderAt_eq_int_iff (n := -1)
    (inverse_meromorphicAt T hT center hne hF)).mpr
  refine ⟨desingularizedInverse T hT center hne,
    desingularizedInverse_analyticAt T hT center hne hF, ?_, ?_⟩
  · rw [desingularizedInverse_center]
    exact (poleResidue_ne_zero_iff T center hne).mpr hN
  · filter_upwards [eventually_desingularizedInverse_eq T hT center hne hF,
      self_mem_nhdsWithin] with z h hz
    rw [h, zpow_neg_one, smul_smul,
      inv_mul_cancel₀ (sub_ne_zero.mpr (show z ≠ (center : ℂ) from hz)), one_smul]

end
end ArtinMatthews.HilbertResolvent
