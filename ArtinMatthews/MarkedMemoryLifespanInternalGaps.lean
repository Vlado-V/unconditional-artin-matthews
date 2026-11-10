module

public import ArtinMatthews.MarkedMemoryTiltPrimewise
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal consecutive gaps of a finite active-visit set partition
all its internal inactive vertices. Their damping products therefore
multiply to the exact internal factor, including empty adjacent gaps. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev MarkedMemoryActiveGap {N : ℕ} (A : Finset (Fin (N+1))) :=
  {e : Fin (N+1) × Fin (N+1) // e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 < e.2 ∧
    ∀ v ∈ A, ¬(e.1 < v ∧ v < e.2)}

def markedMemoryGapVertices {N : ℕ} {A : Finset (Fin (N+1))}
    (e : MarkedMemoryActiveGap A) : Finset (Fin (N+1)) :=
  Finset.univ.filter (fun v => e.1.1 < v ∧ v < e.1.2)

theorem markedMemoryGap_mem_internal {N : ℕ} (A : Finset (Fin (N+1))) (hA : A.Nonempty)
    (e : MarkedMemoryActiveGap A) (v : Fin (N+1)) (hv : v ∈ markedMemoryGapVertices e) :
    v ∈ markedMemoryInternal A (A.min' hA) (A.max' hA) := by
  have hv' := (Finset.mem_filter.mp hv).2
  have hleft := A.min'_le e.1.1 e.2.1
  have hright := A.le_max' e.1.2 e.2.2.1
  have hnot : v ∉ A := fun hm => e.2.2.2.2 v hm hv'
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    exact ⟨lt_of_le_of_lt hleft hv'.1, lt_of_lt_of_le hv'.2 hright, hnot⟩⟩

theorem markedMemoryGap_unique {N : ℕ} {A : Finset (Fin (N+1))}
    (e f : MarkedMemoryActiveGap A) (v : Fin (N+1))
    (he : v ∈ markedMemoryGapVertices e) (hf : v ∈ markedMemoryGapVertices f) : e = f := by
  have he' := (Finset.mem_filter.mp he).2
  have hf' := (Finset.mem_filter.mp hf).2
  have hl : e.1.1 = f.1.1 := by
    apply le_antisymm
    · by_contra hn
      have hfe : f.1.1 < e.1.1 := lt_of_not_ge hn
      exact f.2.2.2.2 e.1.1 e.2.1 ⟨hfe, he'.1.trans hf'.2⟩
    · by_contra hn
      have hef : e.1.1 < f.1.1 := lt_of_not_ge hn
      exact e.2.2.2.2 f.1.1 f.2.1 ⟨hef, hf'.1.trans he'.2⟩
  have hr : e.1.2 = f.1.2 := by
    apply le_antisymm
    · by_contra hn
      have hfe : f.1.2 < e.1.2 := lt_of_not_ge hn
      exact e.2.2.2.2 f.1.2 f.2.2.1 ⟨he'.1.trans hf'.2, hfe⟩
    · by_contra hn
      have hef : e.1.2 < f.1.2 := lt_of_not_ge hn
      exact f.2.2.2.2 e.1.2 e.2.2.1 ⟨hf'.1.trans he'.2, hef⟩
  apply Subtype.ext
  exact Prod.ext hl hr

theorem markedMemoryInternal_mem_gap {N : ℕ} (A : Finset (Fin (N+1))) (hA : A.Nonempty)
    (v : Fin (N+1)) (hv : v ∈ markedMemoryInternal A (A.min' hA) (A.max' hA)) :
    ∃ e : MarkedMemoryActiveGap A, v ∈ markedMemoryGapVertices e := by
  have hv' := (Finset.mem_filter.mp hv).2
  have hbefore : (A.filter (fun b => b < v)).Nonempty :=
    ⟨A.min' hA, Finset.mem_filter.mpr ⟨A.min'_mem hA, hv'.1⟩⟩
  have hafter : (A.filter (fun c => v < c)).Nonempty :=
    ⟨A.max' hA, Finset.mem_filter.mpr ⟨A.max'_mem hA, hv'.2.1⟩⟩
  let b := (A.filter (fun b => b < v)).max' hbefore
  let c := (A.filter (fun c => v < c)).min' hafter
  have hb := Finset.mem_filter.mp ((A.filter (fun b => b < v)).max'_mem hbefore)
  have hc := Finset.mem_filter.mp ((A.filter (fun c => v < c)).min'_mem hafter)
  have hgap : ∀ w ∈ A, ¬(b < w ∧ w < c) := by
    intro w hw hbw
    by_cases hlt : w < v
    · have hwle : w ≤ b := (A.filter (fun b => b < v)).le_max' w
        (Finset.mem_filter.mpr ⟨hw, hlt⟩)
      exact (not_lt_of_ge hwle) hbw.1
    · have hne : w ≠ v := fun he => hv'.2.2 (he ▸ hw)
      have hgt : v < w := by omega
      have hcle : c ≤ w := (A.filter (fun c => v < c)).min'_le w
        (Finset.mem_filter.mpr ⟨hw, hgt⟩)
      exact (not_lt_of_ge hcle) hbw.2
  refine ⟨⟨(b,c), hb.1, hc.1, hb.2.trans hc.2, hgap⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.2, hc.2⟩

/-- Unique consecutive-gap coverage is proved from actual finite minima
and maxima; no pre-existing gap cover or enumeration is assumed. -/
theorem markedMemoryInternal_iff_unique_gap {N : ℕ} (A : Finset (Fin (N+1))) (hA : A.Nonempty)
    (v : Fin (N+1)) :
    v ∈ markedMemoryInternal A (A.min' hA) (A.max' hA) ↔
      ∃! e : MarkedMemoryActiveGap A, v ∈ markedMemoryGapVertices e := by
  constructor
  · intro hv
    obtain ⟨e,he⟩ := markedMemoryInternal_mem_gap A hA v hv
    exact ⟨e,he,fun f hf => markedMemoryGap_unique f e v hf he⟩
  · rintro ⟨e,he,_⟩
    exact markedMemoryGap_mem_internal A hA e v he

theorem markedMemoryInternal_product_gaps {N : ℕ} (A : Finset (Fin (N+1))) (hA : A.Nonempty)
    (f : Fin (N+1) → ℝ) :
    (∏ v ∈ markedMemoryInternal A (A.min' hA) (A.max' hA), f v) =
      ∏ e : MarkedMemoryActiveGap A, ∏ v ∈ markedMemoryGapVertices e, f v := by
  classical
  calc
    _ = ∏ v : Fin (N+1), if v ∈ markedMemoryInternal A (A.min' hA) (A.max' hA) then f v else 1 :=
      (Finset.prod_ite_mem_eq _ _).symm
    _ = ∏ v : Fin (N+1), ∏ e : MarkedMemoryActiveGap A,
        if v ∈ markedMemoryGapVertices e then f v else 1 := by
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ markedMemoryInternal A (A.min' hA) (A.max' hA)
      · rw [ite_eq_left hv]
        obtain ⟨e,he,hu⟩ := (markedMemoryInternal_iff_unique_gap A hA v).mp hv
        symm
        calc
          _ = (if v ∈ markedMemoryGapVertices e then f v else 1) := by
            apply Finset.prod_eq_single e
            · intro d _ hde
              exact ite_eq_right (fun hd => hde (hu d hd))
            · simp
          _ = f v := ite_eq_left he
      · rw [ite_eq_right hv]
        symm
        apply Finset.prod_eq_one
        intro e _
        exact ite_eq_right (fun he => hv (markedMemoryGap_mem_internal A hA e v he))
    _ = ∏ e : MarkedMemoryActiveGap A, ∏ v : Fin (N+1),
        if v ∈ markedMemoryGapVertices e then f v else 1 := Finset.prod_comm
    _ = _ := by simp only [Finset.prod_ite_mem_eq]

end
end ArtinMatthews
