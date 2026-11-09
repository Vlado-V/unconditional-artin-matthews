module

public import OAI.Analysis.PDE.Weak.Elliptic.InteriorRegularity
public import OAI.Analysis.PDE.Weak.Elliptic.RegularityProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine elliptic bootstrap for a smooth bounded zeroth-order
potential.  The forcing is the unknown L² value times the potential; no
smoothness of that forcing or of the unknown is assumed. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational
namespace ArtinMatthews

theorem spectralElliptic_potential_regular_near_point
    (B : (Fin 2 → ℝ) → ℝ →L[ℝ] ℝ) (hB : SmoothBounded B)
    {M : ℝ} (hBM : ∀ x, ‖B x‖ ≤ M)
    (p : H1Pair 1) (hp : p ∈ H1Zero (univ : Set (Fin 2 → ℝ)))
    {Ω : Set (Fin 2 → ℝ)} (hΩ : IsOpen Ω)
    (he : WeakDivergenceEquation Ω p.2
      (fieldMultiplierCLM B hB.1.continuous.aestronglyMeasurable (Eventually.of_forall hBM) p.1))
    (k : ℕ) {x : Fin 2 → ℝ} (hx : x ∈ Ω) :
    ∃ V : Set (Fin 2 → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ H1Regularity V k p := by
  let A : (Fin 2 → ℝ) → CellVectors 1 →L[ℝ] CellVectors 1 :=
    fun _ => ContinuousLinearMap.id ℝ (CellVectors 1)
  have hA : SmoothBounded A := smoothBounded_const (ContinuousLinearMap.id ℝ (CellVectors 1))
  induction k with
  | zero => exact ⟨Ω,hΩ,hx,subset_refl _,trivial⟩
  | succ k ih =>
    obtain ⟨U,hU,hxU,hUΩ,hreg⟩ := ih
    have hf := hreg.value.operator_mul B hB hBM
    have heU : WeakDivergenceEquation U (fun y => A y (p.2 y))
        (fieldMultiplierCLM B hB.1.continuous.aestronglyMeasurable (Eventually.of_forall hBM) p.1) := by
      exact weakEquation_congr_on he hUΩ (Eventually.of_forall fun _ _ => rfl)
        (Eventually.of_forall fun _ _ => rfl)
    have hell : ∀ y ∈ U, ∀ z, (1 : ℝ)*‖z‖^2 ≤ inner ℝ (A y z) z := by
      intro y _ z
      simp only [A,ContinuousLinearMap.id_apply,one_mul,real_inner_self_eq_norm_sq]
      exact le_refl _
    obtain ⟨V,hV,hxV,hVU,hnext⟩ := interior_regular_near_point A hA (by norm_num) k
      hU hell p hp _ hf heU hxU
    exact ⟨V,hV,hxV,hVU.trans hUΩ,hnext⟩

end ArtinMatthews
