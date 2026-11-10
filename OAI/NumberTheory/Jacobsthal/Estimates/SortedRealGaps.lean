module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Sort
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosMarkedStrips

noncomputable def gapLeft (E : Finset ℝ) (i : Fin (E.card-1)) : ℝ :=
  E.orderEmbOfFin rfl ⟨i.val,by have h := i.isLt; omega⟩

noncomputable def gapRight (E : Finset ℝ) (i : Fin (E.card-1)) : ℝ :=
  E.orderEmbOfFin rfl ⟨i.val+1,by have h := i.isLt; omega⟩

theorem gapLeft_mem (E : Finset ℝ) (i : Fin (E.card-1)) : gapLeft E i ∈ E :=
  E.orderEmbOfFin_mem rfl _

theorem gapRight_mem (E : Finset ℝ) (i : Fin (E.card-1)) : gapRight E i ∈ E :=
  E.orderEmbOfFin_mem rfl _

theorem gap_lt (E : Finset ℝ) (i : Fin (E.card-1)) : gapLeft E i < gapRight E i := by
  apply (E.orderEmbOfFin rfl).strictMono
  change i.val < i.val+1
  omega

theorem no_mark_in_gap (E : Finset ℝ) (i : Fin (E.card-1)) {x : ℝ}
    (hx : x ∈ Ioo (gapLeft E i) (gapRight E i)) : x ∉ E := by
  intro hE
  obtain ⟨j,hj⟩ := (E.range_orderEmbOfFin rfl).symm.subset hE
  have hl : gapLeft E i < E.orderEmbOfFin rfl j := by simpa only [hj] using hx.1
  have hh : E.orderEmbOfFin rfl j < gapRight E i := by simpa only [hj] using hx.2
  have hlo := (E.orderEmbOfFin rfl).lt_iff_lt.mp hl
  have hhi := (E.orderEmbOfFin rfl).lt_iff_lt.mp hh
  change i.val < j.val at hlo
  change j.val < i.val+1 at hhi
  omega

theorem exists_gap_of_not_mem (E : Finset ℝ) {S x : ℝ} (h0 : 0 ∈ E) (hS : S ∈ E)
    (hx : x ∈ Icc 0 S) (hxE : x ∉ E) :
    ∃ i : Fin (E.card-1), x ∈ Ioo (gapLeft E i) (gapRight E i) := by
  classical
  let e := E.orderEmbOfFin rfl
  obtain ⟨j0,hj0⟩ := (E.range_orderEmbOfFin rfl).symm.subset h0
  obtain ⟨jS,hjS⟩ := (E.range_orderEmbOfFin rfl).symm.subset hS
  have hx0 : 0 < x := lt_of_le_of_ne hx.1 (fun he => hxE (he ▸ h0))
  let A := Finset.univ.filter (fun j : Fin E.card => e j < x)
  have hA : A.Nonempty := ⟨j0,Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,by simpa only [e,hj0] using hx0⟩⟩
  let j := A.max' hA
  have hjA : j ∈ A := A.max'_mem hA
  have hjx : e j < x := (Finset.mem_filter.mp hjA).2
  have hjSlt : j < jS := e.lt_iff_lt.mp (hjx.trans_le (by simpa only [e,hjS] using hx.2))
  have hnext : j.val+1 < E.card := by have hj := jS.isLt; change j.val < jS.val at hjSlt; omega
  let k : Fin E.card := ⟨j.val+1,hnext⟩
  have hnot : ¬e k < x := by
    intro hkx
    have hkA : k ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkx⟩
    have hle : k ≤ j := A.le_max' k hkA
    change j.val+1 ≤ j.val at hle
    omega
  have hxne : x ≠ e k := by
    intro he
    apply hxE
    rw [he]
    exact E.orderEmbOfFin_mem rfl k
  let i : Fin (E.card-1) := ⟨j.val,by omega⟩
  refine ⟨i,?_,?_⟩
  · exact hjx
  · exact lt_of_le_of_ne (le_of_not_gt hnot) hxne

theorem number_of_gaps_le (E : Finset ℝ) : Fintype.card (Fin (E.card-1)) ≤ E.card := by simp

end ErdosMarkedStrips

end

end Erdos970

end OAI
