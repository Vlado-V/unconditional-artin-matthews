module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
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

/-! Finite gluing of actual measurable slices of a quotient map.  Each
new slice contributes only values not represented by earlier slices. -/
namespace ArtinMatthews.SourcePhysical

open Set MeasureTheory
open scoped Classical
noncomputable section
variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

private def sliceUnion {T : Type*} (s : Finset ι) (A : ι → Set T) : Set T :=
  ⋃ i : s, A i.val

private theorem mem_sliceUnion {T : Type*} (s : Finset ι) (A : ι → Set T) (x : T) :
    x ∈ sliceUnion s A ↔ ∃ i ∈ s, x ∈ A i := by
  simp only [sliceUnion, mem_iUnion, Subtype.exists, exists_prop]

private theorem sliceUnion_insert {T : Type*} (s : Finset ι) (i : ι) (A : ι → Set T) :
    sliceUnion (insert i s) A = A i ∪ sliceUnion s A := by
  ext x
  simp only [mem_sliceUnion, Finset.mem_insert, mem_union]
  constructor
  · rintro ⟨j, rfl | hj, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨j, hj, hx⟩
  · rintro (hx | ⟨j, hj, hx⟩)
    · exact ⟨i, Or.inl rfl, hx⟩
    · exact ⟨j, Or.inr hj, hx⟩

private theorem sliceUnion_measurable {T : Type*} [MeasurableSpace T]
    (s : Finset ι) (A : ι → Set T) (hA : ∀ i, MeasurableSet (A i)) :
    MeasurableSet (sliceUnion s A) := MeasurableSet.iUnion (fun i : s => hA i.val)

theorem exists_measurable_finite_section (q : X → Y) (hq : Measurable q)
    (s : Finset ι) (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hQA : ∀ i, MeasurableSet (q '' A i)) (hi : ∀ i, InjOn q (A i)) :
    ∃ D : Set X, MeasurableSet D ∧ D ⊆ ⋃ i : s, A i.val ∧
      InjOn q D ∧ q '' D = ⋃ i : s, q '' A i.val := by
  change ∃ D : Set X, MeasurableSet D ∧ D ⊆ sliceUnion s A ∧
    InjOn q D ∧ q '' D = sliceUnion s (fun i => q '' A i)
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨∅, MeasurableSet.empty, empty_subset _, injOn_empty q, ?_⟩
    ext y
    simp [mem_sliceUnion]
  | @insert a s ha ih =>
    obtain ⟨D, hD, hsub, hI, hImage⟩ := ih
    let N := A a \ q ⁻¹' (q '' D)
    have hMeas : MeasurableSet (q '' D) := by
      rw [hImage]
      exact sliceUnion_measurable s _ hQA
    refine ⟨D ∪ N, hD.union ((hA a).diff (hq hMeas)), ?_, ?_, ?_⟩
    · rw [sliceUnion_insert]
      rintro x (hx | hx)
      · exact Or.inr (hsub hx)
      · exact Or.inl hx.1
    · intro x hx y hy hxy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact hI hx hy hxy
      · exact False.elim (hy.2 ⟨x, hx, hxy⟩)
      · exact False.elim (hx.2 ⟨y, hy, hxy.symm⟩)
      · exact hi a hx.1 hy.1 hxy
    · rw [sliceUnion_insert, ← hImage]
      ext y
      constructor
      · rintro ⟨x, hx | hx, rfl⟩
        · exact Or.inr ⟨x, hx, rfl⟩
        · exact Or.inl ⟨x, hx.1, rfl⟩
      · intro hy
        by_cases hyD : y ∈ q '' D
        · obtain ⟨x, hx, rfl⟩ := hyD
          exact ⟨x, Or.inl hx, rfl⟩
        · rcases hy with ⟨x, hx, rfl⟩ | hy
          · exact ⟨x, Or.inr ⟨hx, hyD⟩, rfl⟩
          · exact False.elim (hyD hy)

end
end ArtinMatthews.SourcePhysical
