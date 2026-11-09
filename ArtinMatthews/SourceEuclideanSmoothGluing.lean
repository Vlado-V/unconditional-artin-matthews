module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Compactness.Lindelof


set_option backward.privateInPublic true
@[expose] public section

/-! A countable subcover gives almost-everywhere equality on the whole
open domain. Full support makes the smooth representatives agree on
every overlap. -/

namespace ArtinMatthews

open MeasureTheory Set Filter
open scoped ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

theorem sourceSmoothRepresentative_unique (μ : Measure E) [μ.IsOpenPosMeasure]
    {U : Set E} (hU : IsOpen U) {f v w : E → ℂ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) (hw : ContDiffOn ℝ (⊤ : ℕ∞) w U)
    (hva : v =ᵐ[μ.restrict U] f) (hwa : w =ᵐ[μ.restrict U] f) :
    EqOn v w U :=
  Measure.eqOn_open_of_ae_eq (hva.trans hwa.symm) hU hv.continuousOn hw.continuousOn

theorem sourceSmoothRepresentative_glue [SecondCountableTopology E]
    (μ : Measure E) [μ.IsOpenPosMeasure] {U : Set E} (hU : IsOpen U) (f : E → ℂ)
    (hlocal : ∀ x ∈ U, ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∃ v : E → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) v W ∧ v =ᵐ[μ.restrict W] f) :
    ∃ v : E → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) v U ∧ v =ᵐ[μ.restrict U] f := by
  classical
  have hcoverData (x : U) := hlocal x.val x.property
  choose W hWo hxW hWU v hv hva using hcoverData
  let w (x : E) : ℂ := if hx : x ∈ U then v ⟨x,hx⟩ x else 0
  have hagree (a b : U) : EqOn (v a) (v b) (W a ∩ W b) :=
    sourceSmoothRepresentative_unique μ ((hWo a).inter (hWo b))
      ((hv a).mono inter_subset_left) ((hv b).mono inter_subset_right)
      (ae_restrict_of_ae_restrict_of_subset inter_subset_left (hva a))
      (ae_restrict_of_ae_restrict_of_subset inter_subset_right (hva b))
  have hlocalw (a : U) : EqOn w (v a) (W a) := by
    intro x hx
    have hxU := hWU a hx
    change (if h : x ∈ U then v ⟨x,h⟩ x else 0) = v a x
    rw [dite_eq_left hxU]
    exact hagree ⟨x,hxU⟩ a ⟨hxW ⟨x,hxU⟩,hx⟩
  refine ⟨w,contDiffOn_of_locally_contDiffOn ?_,(ae_restrict_iff' hU.measurableSet).mpr ?_⟩
  · intro x hx
    let a : U := ⟨x,hx⟩
    exact ⟨W a,hWo a,hxW a,((hv a).congr (hlocalw a)).mono inter_subset_right⟩
  · have hcover : U ⊆ ⋃ a, W a := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxW ⟨x,hx⟩⟩
    obtain ⟨r,hr,hsub⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover W hWo hcover
    letI : Countable r := hr.to_subtype
    have hrep : ∀ᵐ x ∂μ, ∀ a : r, x ∈ W a.val → v a.val x = f x :=
      ae_all_iff.mpr fun a => (ae_restrict_iff' (hWo a.val).measurableSet).mp (hva a.val)
    filter_upwards [hrep] with x hx
    intro hxU
    obtain ⟨a,ha,hxWa⟩ := mem_iUnion₂.mp (hsub hxU)
    exact (hlocalw a hxWa).trans (hx ⟨a,ha⟩ hxWa)

end
end ArtinMatthews
