module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import ArtinMatthews.DiscreteQuotientSlices
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! For a discrete quotient with a compact covering set, its actual
coinduced measurable space is its Borel space. The forward implication
uses finitely many open quotient slices, not a Borel selection premise. -/
namespace ArtinMatthews.SourcePhysical

open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable (Γ : Subgroup G) [DiscreteTopology Γ]
variable [MeasurableSpace G] [BorelSpace G]

theorem compact_cover_quotient_borel (C : Set G) (hC : IsCompact C)
    (hQ : ((↑) : G → G ⧸ Γ) '' C = univ) : BorelSpace (G ⧸ Γ) := by
  obtain ⟨U, hU, h1, hI⟩ := exists_discrete_quotient_slice Γ
  let T (g : G) : Set G := (fun x => g * x) '' U
  have hT (g : G) : IsOpen (T g) := isOpenMap_mul_left g _ hU
  have hTC : C ⊆ ⋃ g, T g := by
    intro x _
    exact mem_iUnion.mpr ⟨x, 1, h1, mul_one x⟩
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover T hT hTC
  let q : G → G ⧸ Γ := (↑)
  refine ⟨MeasurableSpace.ext ?_⟩
  intro A
  constructor
  · intro hA
    have hP : MeasurableSet (q ⁻¹' A) := hA
    let B := q ⁻¹' A ∩ C
    have hB : MeasurableSet B := hP.inter hC.isClosed.measurableSet
    have hE : A = ⋃ i : s, q '' (B ∩ T i.val) := by
      ext y
      constructor
      · intro hy
        have hyC : y ∈ q '' C := by
          change y ∈ ((↑) : G → G ⧸ Γ) '' C
          rw [hQ]
          exact mem_univ _
        obtain ⟨x, hx, rfl⟩ := hyC
        obtain ⟨g, hg⟩ := mem_iUnion.mp (hs hx)
        obtain ⟨hgs, hxg⟩ := mem_iUnion.mp hg
        exact mem_iUnion.mpr ⟨⟨g, hgs⟩, x, ⟨⟨hy, hx⟩, hxg⟩, rfl⟩
      · intro hy
        obtain ⟨i, hi⟩ := mem_iUnion.mp hy
        obtain ⟨x, hx, rfl⟩ := hi
        exact hx.1.1
    let : MeasurableSpace (G ⧸ Γ) := borel _
    let : BorelSpace (G ⧸ Γ) := ⟨rfl⟩
    change MeasurableSet A
    rw [hE]
    exact MeasurableSet.iUnion fun i : s =>
      quotient_slice_image_measurable Γ (T i.val) B (hT i.val) (hI i.val) hB
  · intro hA
    change MeasurableSet (q ⁻¹' A)
    let : MeasurableSpace (G ⧸ Γ) := borel _
    let : BorelSpace (G ⧸ Γ) := ⟨rfl⟩
    exact QuotientGroup.continuous_mk.measurable (f := q) hA

end
end ArtinMatthews.SourcePhysical
