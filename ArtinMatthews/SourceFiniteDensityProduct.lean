module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal
noncomputable section

theorem finite_lintegral_product_fin {n : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Fin n → Measure α) [∀ i, SigmaFinite (μ i)]
    (w : Fin n → α → ℝ≥0∞) (hw : ∀ i, Measurable (w i)) :
    (∫⁻ x : Fin n → α, ∏ i, w i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, w i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : α × (Fin n → α), w 0 x.1 * ∏ i : Fin n, w i.succ (x.2 i)
          ∂(μ 0).prod (Measure.pi (fun i : Fin n => μ i.succ)) := by
        rw [((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_map_equiv]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, w 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, w i.succ x ∂μ i.succ := by
        have hrest : Measurable (fun x : Fin n → α => ∏ i : Fin n, w i.succ (x i)) :=
          Finset.measurable_prod _ (fun i _ => (hw i.succ).comp (measurable_pi_apply i))
        rw [lintegral_prod_mul (hw 0).aemeasurable hrest.aemeasurable, ih _ _ (fun i => hw i.succ)]
      _ = _ := by rw [Fin.prod_univ_succ]

theorem finite_lintegral_product {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)]
    (w : ι → α → ℝ≥0∞) (hw : ∀ i, Measurable (w i)) :
    (∫⁻ x : ι → α, ∏ i, w i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, w i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [(measurePreserving_piCongrLeft μ e).lintegral_map_equiv]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact finite_lintegral_product_fin _ _ (fun i => hw (e i))

theorem finite_pi_withDensity {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)]
    (w : ι → α → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    [∀ i, SigmaFinite ((μ i).withDensity (w i))] :
    Measure.pi (fun i => (μ i).withDensity (w i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, w i (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ x : ι → α, ∏ i, w i (x i) ∂(Measure.pi μ).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  rw [finite_lintegral_product _ _ hw]
  apply Finset.prod_congr rfl
  intro i _
  exact (withDensity_apply (w i) (hs i)).symm

end
end ArtinMatthews.SourceHyperbolicGreen
