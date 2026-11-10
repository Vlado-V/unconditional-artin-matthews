module

public import ArtinMatthews.MarkedMemoryLifespanQueueSchedule
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

/-! Empty endpoint queues force an even first time and an odd last
time to be actual active occurrences. These are consequences of the
local queue laws; no occurrence/coverage premise is supplied. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {A : Type*} [DecidableEq A] {n : ℕ}
  (d : MarkedMemoryQueueLifespanData A (2*n+1))

omit [DecidableEq A] in
theorem markedMemoryLifespan_first_even_active (hempty : d.initial=[])
    (a : A) (he : d.first a%2=0) : d.active (d.first a) a := by
  by_cases hz : d.first a=0
  · rw [hz]
    by_contra hn
    have hm := (d.initial_mem a).mpr ⟨hz.le,Nat.zero_le _,hn⟩
    rw [hempty] at hm
    exact List.not_mem_nil hm
  · let t := d.first a-1
    have hf : t+1=d.first a := by dsimp [t]; omega
    have ht : t<2*n+1 := by
      have hh := (d.nonempty a).trans (d.bounded a)
      dsimp [t]
      omega
    have ho : t%2=1 := by dsimp [t]; omega
    have hi := d.edge_births t ht ho a hf.symm
    rw [← hf]
    exact (d.edge_active t ht ho a).mpr (Or.inr hi)

theorem markedMemoryLifespan_last_odd_active
    (hempty : markedMemoryPendingQueueAt d (2*n+1)=[])
    (a : A) (ho : d.last a%2=1) : d.active (d.last a) a := by
  by_cases hz : d.last a=2*n+1
  · by_contra hn
    have hm := (markedMemoryPendingQueueAt_mem d (2*n+1) (Nat.le_refl _) a).mpr
      ⟨(d.nonempty a).trans hz.le,by omega,by simpa only [← hz] using hn⟩
    rw [hempty] at hm
    exact List.not_mem_nil hm
  · have ht : d.last a<2*n+1 := lt_of_le_of_ne (d.bounded a) hz
    have hd := d.edge_deaths (d.last a) ht ho a rfl
    simpa only [← hd] using d.edge_outgoing_active (d.last a) ht ho

end
end ArtinMatthews
