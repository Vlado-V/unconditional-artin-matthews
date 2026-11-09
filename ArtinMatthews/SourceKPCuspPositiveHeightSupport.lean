module

public import ArtinMatthews.SourceKPCuspProductMeasure
public import Mathlib.MeasureTheory.Measure.OpenPos


set_option backward.privateInPublic true
@[expose] public section

/-! The actual product height measure sees every neighborhood of a
strictly positive height. Compact height tests therefore determine
continuous functions pointwise on the positive locus. -/

namespace ArtinMatthews
open NumberField MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]
local notation "V" => InfinitePlace K
abbrev sourceKPCuspPositiveHeights : Set (V → ℝ) :=
  {y | ∀ v, 0 < y v}

local notation "P" => sourceKPCuspPositiveHeights K

theorem sourceKPCuspPositiveHeights_isOpen : IsOpen P := by
  rw [show P = Set.univ.pi (fun _ : V => Ioi (0 : ℝ)) by
    ext y
    simp [sourceKPCuspPositiveHeights]]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi

theorem sourceKPCuspPositiveHeights_compact_nhds (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    ∃ B : Set (V → ℝ), IsCompact B ∧ B ∈ 𝓝 y ∧ B ⊆ P := by
  classical
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    ((sourceKPCuspPositiveHeights_isOpen K).mem_nhds hy)
  exact ⟨Metric.closedBall y (r/2), isCompact_closedBall _ _,
    Metric.closedBall_mem_nhds _ (half_pos hr),
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hsub⟩

private theorem sourceKPCuspHeightMeasure_pos_of_open {O : Set ℝ}
    (hO : IsOpen O) (hpos : O ⊆ Ioi (0 : ℝ)) (hne : O.Nonempty) :
    0 < sourceKPCuspHeightMeasure O := by
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((t ^ 3)⁻¹)
  have hf : Measurable f := by fun_prop
  have hs : Function.support f ∩ O ∩ Ioi (0 : ℝ) = O := by
    ext t
    constructor
    · exact fun ht => ht.1.2
    · intro ht
      have htpos : 0 < t := hpos ht
      exact ⟨⟨(ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos htpos 3))).ne', ht⟩, htpos⟩
  change 0 < ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity f O
  rw [withDensity_apply _ hO.measurableSet, setLIntegral_pos_iff hf,
    Measure.restrict_apply ((measurableSet_support hf).inter hO.measurableSet), hs]
  exact hO.measure_pos volume hne

theorem sourceKPCuspProductHeightMeasure_pos_of_nhds
    {y : V → ℝ} (hy : ∀ v, 0 < y v) {B : Set (V → ℝ)} (hB : B ∈ 𝓝 y) :
    0 < sourceKPCuspProductHeightMeasure K B := by
  classical
  obtain ⟨O, hOB, hO, hyO⟩ := mem_nhds_iff.mp hB
  obtain ⟨u, hu, huO⟩ := isOpen_pi_iff'.mp hO y hyO
  let s (v : V) := u v ∩ Ioi (0 : ℝ)
  have hs : Set.univ.pi s ⊆ B :=
    (Set.pi_mono fun v _ => inter_subset_left (s := u v) (t := Ioi (0 : ℝ))).trans (huO.trans hOB)
  have hp (v : V) : 0 < sourceKPCuspHeightMeasure (s v) :=
    sourceKPCuspHeightMeasure_pos_of_open ((hu v).1.inter isOpen_Ioi) inter_subset_right
      ⟨y v, (hu v).2, hy v⟩
  apply lt_of_lt_of_le _ (measure_mono hs)
  rw [sourceKPCuspProductHeightMeasure, Measure.pi_pi]
  exact pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun v _ => (hp v).ne')

theorem sourceKPCuspPositiveHeights_eq_of_compact_ae
    (f g : (V → ℝ) → ℂ) (hf : ContinuousOn f P) (hg : ContinuousOn g P)
    (hae : ∀ (B : Set (V → ℝ)), IsCompact B → B ⊆ P →
      f =ᵐ[(sourceKPCuspProductHeightMeasure K).restrict B] g)
    (y : V → ℝ) (hy : ∀ v, 0 < y v) : f y = g y := by
  have hP := (sourceKPCuspPositiveHeights_isOpen K).mem_nhds hy
  obtain ⟨B, hBc, hBy, hBP⟩ := sourceKPCuspPositiveHeights_compact_nhds K y hy
  by_contra hn
  have hcont := (hf.continuousAt hP).prodMk (hg.continuousAt hP)
  have hne : {z | f z ≠ g z} ∈ 𝓝 y :=
    hcont (isClosed_diagonal.isOpen_compl.mem_nhds hn)
  have hnull : sourceKPCuspProductHeightMeasure K ({z | f z ≠ g z} ∩ B) = 0 := by
    have h := hae B hBc hBP
    change (∀ᵐ z ∂(sourceKPCuspProductHeightMeasure K).restrict B, f z = g z) at h
    rwa [ae_iff, Measure.restrict_apply' hBc.measurableSet] at h
  exact (sourceKPCuspProductHeightMeasure_pos_of_nhds K hy (inter_mem hne hBy)).ne' hnull

end
end ArtinMatthews
