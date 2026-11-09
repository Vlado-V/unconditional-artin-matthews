module

public import ArtinMatthews.SourceKPCuspProductMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! The native height product is supported on positive heights and is
exhausted by compact positive boxes. -/
namespace ArtinMatthews
open NumberField MeasureTheory Set
open scoped ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K]
local notation "V" => InfinitePlace K
local notation "ν" => sourceKPCuspProductHeightMeasure K

theorem sourceKPCuspProductHeight_ae_positive :
    ∀ᵐ y ∂ν, ∀ v : V, 0 < y v := by
  have h : ∀ᵐ z ∂sourceKPCuspHeightMeasure, z ∈ Ioi (0 : ℝ) :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  refine ae_all_iff.mpr fun v => ?_
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : V => sourceKPCuspHeightMeasure)
    (i := v)).eventually h

theorem sourceKPCuspProductHeight_ae_of_compact (P : (V → ℝ) → Prop)
    (h : ∀ B : Set (V → ℝ), IsCompact B → (∀ y ∈ B, ∀ v, 0 < y v) →
      ∀ᵐ y ∂(ν).restrict B, P y) :
    ∀ᵐ y ∂ν, P y := by
  let B (n : ℕ) : Set (V → ℝ) :=
    Set.univ.pi fun _ => Icc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 1)
  have hB (n : ℕ) : IsCompact (B n) := isCompact_univ_pi fun _ => isCompact_Icc
  have hp (n : ℕ) (y : V → ℝ) (hy : y ∈ B n) (v : V) : 0 < y v :=
    (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹).trans_le (hy v (mem_univ v)).1
  have hcover : (⋃ n, B n) = {y | ∀ v, 0 < y v} := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := mem_iUnion.mp hy
      exact hp n y hn
    · intro hy
      obtain ⟨M, hM⟩ := (Set.finite_range fun v : V => max (y v) (y v)⁻¹).bddAbove
      obtain ⟨n, hn⟩ := exists_nat_gt M
      refine mem_iUnion.mpr ⟨n, ?_⟩
      intro v _
      have hmax : max (y v) (y v)⁻¹ ≤ (n : ℝ) + 1 :=
        (hM (Set.mem_range_self v)).trans (by linarith)
      exact ⟨(inv_le_comm₀ (by positivity) (hy v)).mpr ((le_max_right _ _).trans hmax),
        (le_max_left _ _).trans hmax⟩
  have hlocal := (ae_restrict_iUnion_iff B P).mpr fun n => h (B n) (hB n) (hp n)
  have hfull : ∀ᵐ y ∂ν, y ∈ ⋃ n, B n := by
    rw [hcover]
    exact sourceKPCuspProductHeight_ae_positive K
  rwa [Measure.restrict_eq_self_of_ae_mem hfull] at hlocal

end
end ArtinMatthews
