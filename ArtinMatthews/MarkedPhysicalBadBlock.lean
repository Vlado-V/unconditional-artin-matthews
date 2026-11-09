module

public import ArtinMatthews.MarkedPhysicalBadBlockDefs
public import ArtinMatthews.MarkedPhysicalFiniteBlock


set_option backward.privateInPublic true
@[expose] public section

/-! Finite physical source-bad pairing domination. The source/target
incidences and original union normalization remain inside the positive
canonical-root majorant. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysical_canonical_source_bad_block_le
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (x d₀ Y Q : ℝ) (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (w : Z → ℤ × ℤ) (hw : ∀ z, markedMinorIntegerDet z.1 (w z) = 1)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (H F G R : ℝ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hG : 0 ≤ G) (hη : ∀ t, ‖η t‖ ≤ H)
    (hY : 0 < Y) (hsupp : ∀ v, ψ v ≠ 0 → |v| ≤ R)
    (f g : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ F) (hg : ∀ s, ‖g s‖ ≤ G)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1))
    [NeZero (markedPhysicalMarkingProduct u)] (hS : Squarefree (markedPhysicalMarkingProduct u))
    {A B C D U : ℝ} (hA : 1 < A) (hC : 1 < C) (hU : 0 < U) (hUA : U ≤ A) (hBU : B ≤ 16*U)
    (hbox : Z ⊆ markedPhysicalPrimitiveBox A B C D)
    (hcover : ∀ θ : AddCircle (1 : ℝ),
      (if θ ∈ markedRawBadRootSet e x d₀ Y (markedPhysicalActualEdgeRawSource e x u) then (1 : ℝ) else 0) ≤
        markedRawBadRootArcMajorant e x d₀ Y (markedPhysicalActualEdgeRawSource e x u) θ) :
    markedPhysicalSourceBadBlock e x d₀ Y Q V Z hZ w ψ η f g u hS (B := B) (D := D) hA hC ≤
      (markedPhysicalMass V (markedPadSlots x+1)*H^2*F*G) *
        markedPhysicalRootIncidenceMajorantSum e x (markedPhysicalActualEdgeRawSource e x u)
          d₀ Y (markedPhysicalMarkingProduct u) A B C D
          (markedPhysicalActualEdgeCopiedDivisor e x u)
          (markedPhysicalActualEdgeSourceProduct e x u)
          (markedPhysicalActualEdgeTargetProduct e x u) R Q ψ (markedPhysicalEdgeRootLineEvent u hS) := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  let c := markedPhysicalMass V (markedPadSlots x+1)*H^2*F*G
  let wt := fun (r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D) z =>
    if markedPhysicalEdgeRootLineEvent u hS r.1 z then
      markedPhysicalCanonicalBadWeight e x d₀ Y Q u r z ψ else 0
  let term := markedPhysicalSourceBadTerm e x d₀ Y Q V Z hZ w ψ η f g u hS (B := B) (D := D) hA hC
  have hc0 : 0 ≤ c := by
    have hm := markedPhysicalMass_nonneg V (markedPadSlots x+1) hV
    dsimp only [c]
    positivity
  have hwt (r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D) (z : ℤ × ℤ) :
      0 ≤ wt r z := by
    have ha : 0 ≤ markedRawBadRootArcMajorant e x d₀ Y (markedPhysicalActualEdgeRawSource e x u)
        ((((markedPhysicalCanonicalCompletion r).1 : ℝ)/
          ((markedPhysicalCanonicalRootPosition r).1 : ℝ)) : AddCircle (1 : ℝ)) :=
      (by split_ifs <;> norm_num : (0 : ℝ) ≤
        if ((((markedPhysicalCanonicalCompletion r).1 : ℝ)/
          ((markedPhysicalCanonicalRootPosition r).1 : ℝ)) : AddCircle (1 : ℝ)) ∈
          markedRawBadRootSet e x d₀ Y (markedPhysicalActualEdgeRawSource e x u) then 1 else 0).trans (hcover _)
    dsimp only [wt, markedPhysicalCanonicalBadWeight]
    split_ifs <;> positivity
  have hterm (r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D)
      (z : ℤ × ℤ) (hz : z ∈ markedPhysicalCanonicalTargets hA hC r Z) :
      ‖term r z‖ ≤ c*(if z ∈ markedPhysicalRootTargetWindow (markedPhysicalActualEdgeCopiedDivisor e x u) R Y
        then wt r z else 0) := by
    have hh := markedPhysical_source_bad_position_norm_le e x d₀ Y Q V hV Z hZ w hw
      ψ η H F G R hH hF hG hη hY hsupp f g hf hg u hA hC hU hUA hBU hbox r z hz hcover
    by_cases he : markedPhysicalEdgeRootLineEvent u hS r.1 z
    · simpa only [term, markedPhysicalSourceBadTerm, wt, c, ite_eq_left he] using hh
    · simp only [term, markedPhysicalSourceBadTerm, wt, ite_eq_right he, norm_zero, ite_self, mul_zero, le_refl]
  have hfinite := markedPhysical_finite_block_le
    (fun r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D =>
      markedPhysicalCanonicalTargets hA hC r Z)
    (markedPhysicalRootTargetWindow (markedPhysicalActualEdgeCopiedDivisor e x u) R Y)
    term wt c hc0 (fun r z hz => by
      have hh := hterm r z hz
      by_cases ht : z ∈ markedPhysicalRootTargetWindow (markedPhysicalActualEdgeCopiedDivisor e x u) R Y
      · simpa only [ite_eq_left ht] using hh
      · simpa only [ite_eq_right ht] using hh) (fun r z _ => hwt r z)
  have hsum : (∑ r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D,
      ∑ z ∈ markedPhysicalRootTargetWindow (markedPhysicalActualEdgeCopiedDivisor e x u) R Y, wt r z) =
      markedPhysicalRootIncidenceMajorantSum e x (markedPhysicalActualEdgeRawSource e x u) d₀ Y
        (markedPhysicalMarkingProduct u) A B C D
        (markedPhysicalActualEdgeCopiedDivisor e x u)
        (markedPhysicalActualEdgeSourceProduct e x u)
        (markedPhysicalActualEdgeTargetProduct e x u) R Q ψ (markedPhysicalEdgeRootLineEvent u hS) := by
    simpa only [wt, markedPhysicalCanonicalBadWeight] using
      markedPhysicalCanonicalWeight_sum e x (markedPhysicalActualEdgeRawSource e x u) d₀ Y
        (markedPhysicalMarkingProduct u) A B C D
        (markedPhysicalActualEdgeCopiedDivisor e x u)
        (markedPhysicalActualEdgeSourceProduct e x u)
        (markedPhysicalActualEdgeTargetProduct e x u) R Q ψ (markedPhysicalEdgeRootLineEvent u hS)
  rw [hsum] at hfinite
  exact hfinite

end ArtinMatthews
