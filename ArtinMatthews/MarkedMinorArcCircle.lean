module

public import ArtinMatthews.MarkedMinorArcSmoothOperator
public import ArtinMatthews.MarkedMinorArcProductFourier
public import Mathlib.Analysis.Normed.Group.AddCircle
public import ArtinMatthews.MarkedMinorArcProductEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The actual smooth determinant fiber on the normalized frequency circle,
restricted to the actual complement of rational major arcs. -/
namespace ArtinMatthews
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Literal periodic major arcs, including every rational of allowed reduced
denominator, with the same radius as the real-representative definition. -/
def markedMinorCircleMajor (Q Y : ℝ) : Set (AddCircle (1:ℝ)) :=
  ⋃ r : ℚ, if (r.den : ℝ) ≤ Q then
    Metric.closedBall (((r : ℝ) : AddCircle (1:ℝ))) (2*Q/Y) else ∅

theorem markedMinorCircleMajor_measurable (Q Y : ℝ) :
    MeasurableSet (markedMinorCircleMajor Q Y) := by
  unfold markedMinorCircleMajor
  apply MeasurableSet.iUnion
  intro r
  split_ifs
  · exact Metric.isClosed_closedBall.measurableSet
  · exact MeasurableSet.empty

/-- A frequency outside the periodic major arcs has every real representative
outside the actual rational arcs used by the checked Diophantine estimate. -/
theorem markedMinorCircleMajor_real {θ Q Y : ℝ}
    (h : (θ : AddCircle (1:ℝ)) ∉ markedMinorCircleMajor Q Y) :
    ¬MarkedInMajorArcs θ Q Y := by
  rintro ⟨r,hr,hd⟩
  apply h
  unfold markedMinorCircleMajor
  apply Set.mem_iUnion.mpr
  refine ⟨r, ?_⟩
  rw [ite_eq_left hr]
  have hn : ‖((θ-(r:ℝ) : ℝ) : AddCircle (1:ℝ))‖ ≤ |θ-(r:ℝ)| :=
    QuotientAddGroup.norm_mk_le_norm
  rw [Metric.mem_closedBall,dist_eq_norm,← QuotientAddGroup.mk_sub]
  exact hn.trans hd

/-- The actual integer determinant Fourier matrix on the circle. -/
noncomputable def markedMinorSmoothCircleMatrix (ψ : SchwartzMap ℝ ℂ)
    (L T : ℤ) (M N : ℕ) (Y : ℝ) (θ : AddCircle (1:ℝ)) :
    Matrix (MarkedMinorBoxIndex L T M N) (MarkedMinorBoxIndex L T M N) ℂ :=
  fun h l => ((Y : ℂ)⁻¹) *
    (ψ (((h.1.1*l.1.2-h.1.2*l.1.1 : ℤ) : ℝ)/Y) *
      fourier (h.1.1*l.1.2-h.1.2*l.1.1) θ)

/-- The circle convention agrees exactly with the source real exponential. -/
theorem markedMinorSmoothCircleMatrix_coe (ψ : SchwartzMap ℝ ℂ)
    (L T : ℤ) (M N : ℕ) (Y θ : ℝ) :
    markedMinorSmoothCircleMatrix ψ L T M N Y (θ : AddCircle (1:ℝ)) =
      markedMinorSmoothDeterminantMatrix ψ L T M N Y θ := by
  ext h l
  unfold markedMinorSmoothCircleMatrix markedMinorSmoothDeterminantMatrix
  rw [fourier_coe_apply]
  push_cast
  congr 2
  unfold OAI.Problem337.RealPhase.phase
  congr 1
  push_cast
  ring

/-- The literal minor-frequency fiber, equal to zero on the major arcs. -/
noncomputable def markedMinorCircleFiber (ψ : SchwartzMap ℝ ℂ)
    (L T : ℤ) (M N : ℕ) (Y Q : ℝ) (θ : AddCircle (1:ℝ)) :
    Matrix (MarkedMinorBoxIndex L T M N) (MarkedMinorBoxIndex L T M N) ℂ := by
  classical
  exact if θ ∈ markedMinorCircleMajor Q Y then 0 else
    markedMinorSmoothCircleMatrix ψ L T M N Y θ

theorem markedMinorCircleFiber_measurable (ψ : SchwartzMap ℝ ℂ)
    (L T : ℤ) (M N : ℕ) (Y Q : ℝ)
    (h l : MarkedMinorBoxIndex L T M N) :
    AEStronglyMeasurable (fun θ => markedMinorCircleFiber ψ L T M N Y Q θ h l)
      AddCircle.haarAddCircle := by
  have hc : Continuous (fun θ : AddCircle (1:ℝ) =>
      markedMinorSmoothCircleMatrix ψ L T M N Y θ h l) := by
    unfold markedMinorSmoothCircleMatrix
    fun_prop
  classical
  have hm : AEStronglyMeasurable ((markedMinorCircleMajor Q Y)ᶜ.indicator
      (fun θ => markedMinorSmoothCircleMatrix ψ L T M N Y θ h l))
      AddCircle.haarAddCircle :=
    hc.aestronglyMeasurable.indicator (markedMinorCircleMajor_measurable Q Y).compl
  apply hm.congr
  exact Filter.Eventually.of_forall (fun θ => by
    by_cases hθ : θ ∈ markedMinorCircleMajor Q Y
    · simp [Set.indicator,markedMinorCircleFiber,hθ]
    · simp [Set.indicator,markedMinorCircleFiber,hθ])

/-- Actual minor-circle fiber norm, preserving the explicit exponent G+3. -/
theorem marked_minor_circle_fiber_opNorm (ψ : SchwartzMap ℝ ℂ) {G C H : ℝ}
    (hG : 0 < G) (hC : 1 ≤ C) (hH : 1 ≤ H) :
    ∀ᶠ Λ : ℝ in Filter.atTop, ∀ (Y : ℝ) (L T : ℤ) (M N : ℕ),
      Real.exp (Λ^(1/10 : ℝ)) ≤ Y → Y ≤ Real.exp (H*Λ^(1/5 : ℝ)) →
      1 ≤ M → 1 ≤ N → (M : ℝ)*(N : ℝ) ≤ C*Y →
      (M : ℝ) ≤ C*Y^(9/10 : ℝ) → (N : ℝ) ≤ C*Y^(9/10 : ℝ) →
      ∀ θ : AddCircle (1:ℝ),
      ‖markedMinorCircleFiber ψ L T M N Y (Λ^(G+3)) θ‖ ≤ Λ^(-G) := by
  classical
  filter_upwards [marked_minor_smooth_determinant_opNorm ψ hG hC hH,
    Filter.eventually_ge_atTop (1:ℝ)] with Λ hΛ hΛone
  intro Y L T M N hYlo hYhi hMpos hNpos hMN hM hN θ
  unfold markedMinorCircleFiber
  split_ifs with hθ
  · simpa only [norm_zero] using Real.rpow_nonneg (by linarith : (0:ℝ) ≤ Λ) (-G)
  · induction θ using QuotientAddGroup.induction_on
    rename_i θ
    rw [markedMinorSmoothCircleMatrix_coe]
    exact hΛ Y L T M N θ hYlo hYhi hMpos hNpos hMN hM hN
      (markedMinorCircleMajor_real hθ)

end ArtinMatthews
