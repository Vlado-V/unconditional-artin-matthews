module

public import ArtinMatthews.MarkedMemoryPrimeVisitFactors
public import ArtinMatthews.MarkedMemoryPrimeLifespanAnchor
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The literal half-step endpoint scalar, before any product is
partitioned into prefix/internal/suffix intervals. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ} {L : Type*} (eta : Fin (N+1) → ℝ) (line : Fin (N+1) → L)

def markedMemoryPrimeIntervalVisitScalar (A : Finset (Fin (N+1)))
    (c : MarkedMemoryPrimeLifespanChoice N) (v : Fin (N+1)) : ℝ :=
  let first := markedMemoryPrimeFirst A c
  let last := markedMemoryPrimeLast A c
  let hit := markedLineHit line v (line (markedMemoryPrimeBirthVisit A c))
  (if first≤2*v.val ∧ 2*v.val≤last ∧ v∉A then
      (if last=2*v.val then -eta v*hit else 1-eta v*hit) else 1)*
    (if first=2*v.val+1 ∧ 2*v.val+1≤last ∧ v∉A then -eta v*hit else 1)

def markedMemoryPrimeIntervalScalar (A : Finset (Fin (N+1)))
    (c : MarkedMemoryPrimeLifespanChoice N) : ℝ :=
  ∏ v,markedMemoryPrimeIntervalVisitScalar eta line A c v

theorem markedMemoryPrimeIntervalVisitScalar_active (A : Finset (Fin (N+1)))
    (c : MarkedMemoryPrimeLifespanChoice N) (hA : A.Nonempty)
    (hc : MarkedMemoryPrimeLifespanCompatible line A c) (v : Fin (N+1)) :
    markedMemoryPrimeIntervalVisitScalar eta line A c v=
      markedMemoryPrefixVisitFactor eta line (A.min' hA) c.1 v*
        markedMemoryInternalVisitFactor eta line A (A.min' hA) (A.max' hA) v*
          markedMemorySuffixVisitFactor eta line (A.min' hA) (A.max' hA) c.2 v := by
  have hmin := A.min'_mem hA
  have hmax := A.max'_mem hA
  have horder := A.min'_le_max' hA
  have hc' := hc
  rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_left hA] at hc'
  have hline := markedMemoryPrimeBirthVisit_active line A c hc (A.min' hA) hmin
  unfold markedMemoryPrimeIntervalVisitScalar
  rw [hline]
  cases ha : c.1 <;> cases hb : c.2
  all_goals
    try have hl := (hc'.2.1 _ ha).1
    try have hr := (hc'.2.2 _ hb).1
    simp only [markedMemoryPrimeFirst,markedMemoryPrimeLast,ha,hb,dite_eq_left hA,
      markedMemoryPrefixVisitFactor,markedMemoryInternalVisitFactor,markedMemorySuffixVisitFactor,
      markedMemoryPrimeDamping]
    by_cases hv : v∈A
    · have hlo := A.min'_le v hv
      have hhi := A.le_max' v hv
      simp only [hv,not_true_eq_false,and_false,ite_false]
      (try split_ifs) <;> first | omega | ring
    · have hnmin : v≠A.min' hA := by intro hh; exact hv (hh ▸ hmin)
      have hnmax : v≠A.max' hA := by intro hh; exact hv (hh ▸ hmax)
      simp only [hv,not_false_eq_true,and_true]
      (try split_ifs) <;> first | omega | (try simp_all only []; ring)

end
end ArtinMatthews
