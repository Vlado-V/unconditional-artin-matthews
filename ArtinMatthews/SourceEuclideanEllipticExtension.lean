module

public import ArtinMatthews.SourceEuclideanCoefficientCutoff
public import ArtinMatthews.SourceEuclideanCoercivity
public import Mathlib.Analysis.Calculus.MeanValue


set_option backward.privateInPublic true
@[expose] public section

/-! Extend the actual coefficient on a small neighborhood by a constant
outside a compact set. The convex combination preserves coercivity. -/

namespace ArtinMatthews

open Set Filter
open scoped ContDiff Topology SchwartzMap

noncomputable section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem sourceElliptic_extension_uniform (A : E → V →L[ℝ] V) (d : E → ℂ)
    {U : Set E} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hd : ContDiffOn ℝ ∞ d U)
    {x : E} (hx : x ∈ U) {a : ℝ} (ha : 0 < a)
    (hpos : ∀ y ∈ U, ∀ w : V, a*‖w‖*‖w‖ ≤ inner ℝ (A y w) w) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∃ (A' : E → V →L[ℝ] V) (m : 𝓢(E, ℂ)),
        EqOn A' A W ∧ EqOn m d W ∧
        ContDiff ℝ ∞ A' ∧ HasCompactSupport (fun y => A' y - A x) ∧
        (∃ L : NNReal, LipschitzWith L A') ∧ (∃ C : ℝ, ∀ y, ‖A' y‖ ≤ C) ∧
        ∀ y, ∀ w : V, a*‖w‖*‖w‖ ≤ inner ℝ (A' y w) w := by
  obtain ⟨η,hη,hηc,hηU,hηone,hη01⟩ := sourceSmooth_unit_cutoff_near_point hU hx
  obtain ⟨W,hW,hWo,hxW⟩ :=
    mem_nhds_iff.mp (inter_mem (hU.mem_nhds hx) (show {y | η y = 1} ∈ 𝓝 x from hηone))
  let P (y : E) := η y • (A y - A x)
  let A' (y : E) := P y + A x
  let F (y : E) := η y • d y
  have hP : ContDiff ℝ ∞ P := sourceSmooth_supported_smul hU η _ hη hηU (hA.sub contDiffOn_const)
  have hPc : HasCompactSupport P := hηc.smul_right
  have hA' : ContDiff ℝ ∞ A' := hP.add contDiff_const
  have hA'c : HasCompactSupport (fun y => A' y - A x) := by
    simpa only [A',add_sub_cancel_right] using hPc
  have hF : ContDiff ℝ ∞ F := sourceSmooth_supported_smul hU η d hη hηU hd
  have hFc : HasCompactSupport F := hηc.smul_right
  let m := hFc.toSchwartzMap hF
  have hEqA : EqOn A' A W := by
    intro y hy
    change η y • (A y - A x) + A x = A y
    rw [(hW hy).2,one_smul,sub_add_cancel]
  have hEqm : EqOn m d W := by
    intro y hy
    change η y • d y = d y
    rw [(hW hy).2,one_smul]
  refine ⟨W,hWo,hxW,fun _ hy => (hW hy).1,A',m,hEqA,hEqm,hA',hA'c,?_,?_,?_⟩
  · obtain ⟨L,hL⟩ := (hP.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (HasCompactSupport.fderiv ℝ hPc)
    let L' : NNReal := ⟨max 0 L,le_max_left _ _⟩
    refine ⟨L',lipschitzWith_of_nnnorm_fderiv_le (hA'.differentiable (by simp)) (fun y => ?_)⟩
    change ‖fderiv ℝ (fun z => P z + A x) y‖ ≤ max 0 L
    rw [fderiv_add_const]
    exact (hL y).trans (le_max_right _ _)
  · obtain ⟨C,hC⟩ := hP.continuous.bounded_above_of_compact_support hPc
    exact ⟨C+‖A x‖,fun y => (norm_add_le _ _).trans (add_le_add (hC y) le_rfl)⟩
  · intro y w
    by_cases hy : y ∈ U
    · have hAct : A' y w = η y • A y w + (1-η y) • A x w := by
        simp only [A',P,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.sub_apply,smul_sub,sub_smul,one_smul]
        abel
      rw [hAct,inner_add_left,real_inner_smul_left,real_inner_smul_left]
      calc
        _ = η y * (a*‖w‖*‖w‖) + (1-η y) * (a*‖w‖*‖w‖) := by ring
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hpos y hy w) (hη01 y).1)
          (mul_le_mul_of_nonneg_left (hpos x hx w) (sub_nonneg.mpr (hη01 y).2))
    · have hηy : η y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hηU h))
      have he : A' y = A x := by simp only [A',P,hηy,zero_smul,zero_add]
      rw [he]
      exact hpos x hx w

theorem sourceElliptic_extension_at_point (A : E → V →L[ℝ] V) (d : E → ℂ)
    {U : Set E} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hd : ContDiffOn ℝ ∞ d U)
    {x : E} (hx : x ∈ U) {a : ℝ} (ha : 0 < a)
    (hpos : ∀ w : V, a*‖w‖*‖w‖ ≤ inner ℝ (A x w) w) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∃ (A' : E → V →L[ℝ] V) (m : 𝓢(E, ℂ)),
        EqOn A' A W ∧ EqOn m d W ∧
        ContDiff ℝ ∞ A' ∧ HasCompactSupport (fun y => A' y - A x) ∧
        (∃ L : NNReal, LipschitzWith L A') ∧ (∃ C : ℝ, ∀ y, ‖A' y‖ ≤ C) ∧
        ∀ y, ∀ w : V, (a/2)*‖w‖*‖w‖ ≤ inner ℝ (A' y w) w := by
  obtain ⟨U',hU',hx',hU'U,hpos'⟩ :=
    sourceElliptic_coercive_near_point hU hx A hA.continuousOn ha hpos
  obtain ⟨W,hW,hxW,hWU',A',m,hAeq,hmeq,hA',hc,hLip,hbound,hcoercive⟩ :=
    sourceElliptic_extension_uniform A d hU' (hA.mono hU'U) (hd.mono hU'U) hx' (half_pos ha) hpos'
  exact ⟨W,hW,hxW,hWU'.trans hU'U,A',m,hAeq,hmeq,hA',hc,hLip,hbound,hcoercive⟩

end
end ArtinMatthews
