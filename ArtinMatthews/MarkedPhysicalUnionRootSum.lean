module

public import ArtinMatthews.MarkedPhysicalIncidenceRootSum
public import ArtinMatthews.MarkedPhysicalTotalRootError
public import ArtinMatthews.MarkedPhysicalActualUnionMainBound


set_option backward.privateInPublic true
@[expose] public section

/-! The literal positive canonical-root majorant after summing the actual
union labels. Its main term is the proved physical Haar sum and its error
is the proved sum over all actual labels and residue classes. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalActualUnionMajorantSum
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
    (d₀ Y A B C D R Q : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  ∑ u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1),
    if hu : MarkedPhysicalMarkingDistinct u then
      let hP := fun j p (hp : p ∈ markedLogPowerBand (e j) x) => (mem_markedLogPowerBand.mp hp).1
      letI : NeZero (markedPhysicalMarkingProduct u) := ⟨(markedPhysicalMarkingProduct_pos hP u).ne'⟩
      let hS := markedPhysicalMarkingProduct_squarefree hP hdis u hu
      markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x+1) *
        markedPhysicalRootIncidenceMajorantSum e x (markedPhysicalActualEdgeRawSource e x u)
          d₀ Y (markedPhysicalMarkingProduct u) A B C D
          (markedPhysicalActualEdgeCopiedDivisor e x u)
          (markedPhysicalActualEdgeSourceProduct e x u)
          (markedPhysicalActualEdgeTargetProduct e x u) R Q ψ (markedPhysicalEdgeRootLineEvent u hS)
    else 0

theorem markedPhysicalActualUnionMajorantSum_main_error_le
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
    (d₀ Y U V A B C D R Q : ℝ) (ψ : ℝ → ℂ)
    (hA : 1 < A) (hfirst : Y^(-7/10 : ℝ) < 1/2)
    (hbeta : ∀ j, 100*Real.exp (-((Real.log x)^(e j))) < 1/2) :
    markedPhysicalActualUnionMajorantSum e x hdis d₀ Y A B C D R Q ψ/(U*V) ≤
      markedPhysicalActualUnionLineMain e x hdis d₀ Y A B C D R Q ψ/(U*V) +
        markedPhysicalActualTotalRootError e x hdis d₀ Y U V A B C D R Q ψ := by
  have hσ : 0 ≤ markedPhysicalMass
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x+1) := by
    apply markedPhysicalMass_nonneg
    intro j
    unfold bandReciprocalMass
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hd : (markedPhysicalActualUnionMajorantSum e x hdis d₀ Y A B C D R Q ψ -
      markedPhysicalActualUnionLineMain e x hdis d₀ Y A B C D R Q ψ)/(U*V) ≤
        markedPhysicalActualTotalRootError e x hdis d₀ Y U V A B C D R Q ψ := by
    unfold markedPhysicalActualUnionMajorantSum markedPhysicalActualUnionLineMain
      markedPhysicalActualTotalRootError
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_le_sum
    intro u _
    by_cases hu : MarkedPhysicalMarkingDistinct u
    · simp only [dite_eq_left hu]
      let hP := fun j p (hp : p ∈ markedLogPowerBand (e j) x) => (mem_markedLogPowerBand.mp hp).1
      let : NeZero (markedPhysicalMarkingProduct u) := ⟨(markedPhysicalMarkingProduct_pos hP u).ne'⟩
      rw [← mul_sub, mul_div_assoc,
        markedPhysicalRootIncidenceMajorantSum_error_eq e x (markedPhysicalActualEdgeRawSource e x u)
          d₀ Y (markedPhysicalMarkingProduct u) A B C D U V
          (markedPhysicalActualEdgeCopiedDivisor e x u)
          (markedPhysicalActualEdgeSourceProduct e x u)
          (markedPhysicalActualEdgeTargetProduct e x u) R Q ψ
          (markedPhysicalEdgeRootLineEvent u (markedPhysicalMarkingProduct_squarefree hP hdis u hu))
          hA hfirst hbeta]
      apply mul_le_mul_of_nonneg_left _ hσ
      apply Finset.sum_le_sum
      intro g _
      exact le_abs_self _
    · simp only [dite_eq_right hu, sub_self, zero_div, le_refl]
  rw [sub_div] at hd
  linarith

theorem markedPhysicalActualUnionMajorantSum_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e)
    (β H R T : ℝ) (hβ : 0 ≤ β) (heβ : ∀ j, e j ≤ β)
    (hβhi : β+(1/100 : ℝ) < 49/50) (hH : 0 ≤ H) (hR : 0 ≤ R)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
        (d₀ Y U V A B C D Q W : ℝ) (ψ : ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V → U ≤ A → A ≤ B → B ≤ 16*U →
        V ≤ C → C ≤ D → D ≤ 2*V →
        1 ≤ Q → Q ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        1 ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
        0 ≤ W → (∀ v, ‖ψ v‖ ≤ W) → (∀ v, ψ v ≠ 0 → |v| ≤ R) →
        markedPhysicalActualUnionMajorantSum e x hdis d₀ Y A B C D R Q ψ/(U*V) ≤
          (16/(riemannZeta 2).re) * ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) +
            (5*E*W)*x^(-δ/4000) := by
  obtain ⟨E,hE,herror⟩ := markedPhysicalActualTotalRootError_bound e he β H R
    hβ heβ hβhi hH hR hδ
  refine ⟨E,hE,?_⟩
  filter_upwards [herror, markedPhysicalActualUnionLineMain_normalized_bound e he hinj T,
    markedRootArc_actual_widths_eventually e he, eventually_gt_atTop (1 : ℝ)]
    with x hx hmain hwidth hx1
  intro hdis d₀ Y U V A B C D Q W ψ hU hV hUA hAB hB hVC hCD hD
    hQ hQhi hY hYhi hYlo hW hψ hsupp
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hUp : 0 < U := (Real.rpow_pos_of_pos hx0 δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos hx0 δ).trans_le hV
  have hA : 1 < A := ((Real.one_lt_rpow hx1 hδ).trans_le hU).trans_le hUA
  apply (markedPhysicalActualUnionMajorantSum_main_error_le e x hdis d₀ Y U V A B C D R Q ψ
    hA (hwidth.2 Y hYlo).2 (fun j => (hwidth.1 j).2)).trans
  exact add_le_add
    (hmain hdis d₀ Y hYlo U V A B C D hUp hVp hUA hAB hB hVC hCD hD
      R Q W ψ hQ hY hR hW hψ hsupp)
    (hx hdis d₀ Y U V A B C D Q W ψ hU hV hUA hAB hB hVC hCD hD
      hQ hQhi hY hYhi hW hψ)

end ArtinMatthews
