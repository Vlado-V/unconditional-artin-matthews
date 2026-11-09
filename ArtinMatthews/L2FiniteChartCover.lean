module

public import ArtinMatthews.L2FiniteChartCompactness
public import Mathlib.Order.Disjointed


set_option backward.privateInPublic true
@[expose] public section

/-! Finite measurable covers are refined internally before applying local L2 compactness. -/
namespace ArtinMatthews
open MeasureTheory Set
open scoped ENNReal Topology BigOperators
noncomputable section

variable {X : Type*} [MeasurableSpace X]
variable {J : Type*} [Fintype J]

theorem finiteChart_measurable_partition (S : Set X) (hS : MeasurableSet S)
    (U : J → Set X) (hU : ∀ j, MeasurableSet (U j)) (hcover : S ⊆ ⋃ j, U j) :
    ∃ s : J → Set X, (∀ j, MeasurableSet (s j)) ∧
      (Pairwise fun i j => Disjoint (s i) (s j)) ∧ S = ⋃ j, s j ∧ ∀ j, s j ⊆ U j := by
  classical
  let e := Fintype.equivFin J
  let V : Fin (Fintype.card J) → Set X := fun i => S ∩ U (e.symm i)
  let s : J → Set X := fun j => disjointed V (e j)
  have hV (i) : MeasurableSet (V i) := hS.inter (hU (e.symm i))
  have hs (j) : MeasurableSet (s j) :=
    disjointedRec (fun _ i ht => ht.diff (hV i)) (hV (e j))
  refine ⟨s, hs, ?_, ?_, ?_⟩
  · exact fun i j hij => disjoint_disjointed V (e.injective.ne hij)
  · ext x
    constructor
    · intro hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp (hcover hx)
      have hv : x ∈ ⋃ i, V i := mem_iUnion.mpr ⟨e j, by simpa [V] using And.intro hx hxj⟩
      rw [← iUnion_disjointed] at hv
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hv
      exact mem_iUnion.mpr ⟨e.symm i, by simpa [s] using hxi⟩
    · intro hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact (disjointed_subset V (e j) hxj).1
  · intro j x hx
    have h := (disjointed_subset V (e j) hx).2
    simpa [V] using h

variable (μ : Measure X)
variable (Y : J → Type*) [∀ j, MeasurableSpace (Y j)]
variable (ν ρ : ∀ j, Measure (Y j))

theorem finiteChart_cover_l2_isCompact_closure {κ : Type*}
    (S : Set X) (hS : MeasurableSet S)
    (U : J → Set X) (hU : ∀ j, MeasurableSet (U j)) (hcover : S ⊆ ⋃ j, U j)
    (q : ∀ j, Y j → X) (hq : ∀ j, Measurable (q j))
    (C : J → ℝ) (hC : ∀ j, 0 ≤ C j) (hρν : ∀ j, ρ j ≤ ν j)
    (hμ : ∀ j, μ.restrict (U j) ≤ ENNReal.ofReal (C j) • Measure.map (q j) (ρ j))
    (f : κ → HeightL2 μ) (F : ∀ j, κ → HeightL2 (ν j))
    (hf : ∀ j k, ∀ᵐ y ∂ρ j, q j y ∈ U j → f k (q j y) = F j k y)
    (hlocal : ∀ j, IsCompact (closure (range (F j)))) :
    IsCompact (closure (range (fun k => measurableL2Cutoff μ S hS (f k)))) := by
  obtain ⟨s, hs, hd, hsc, hsU⟩ := finiteChart_measurable_partition S hS U hU hcover
  refine finiteChart_l2_isCompact_closure μ Y ν ρ S hS s hs hd hsc q hq C hC hρν
    ?_ f F ?_ hlocal
  · intro j
    exact (Measure.restrict_mono (hsU j) le_rfl).trans (hμ j)
  · intro j k
    filter_upwards [hf j k] with y hy
    exact fun hys => hy (hsU j hys)

end
end ArtinMatthews
