module

public import ArtinMatthews.MarkedMemoryActualFibers
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Even actual transitions preserve every indexed active identity.
Their ordered birth batch is the newly born part of the actual target
pending queue, selected by the computed first time. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

theorem markedMemoryHistoryTrace_active_even {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ) (he : t % 2 = 0) (j : J) (k : Fin (pads+1)) :
    markedMemoryHistoryTraceStep hZ history t (Sum.inl ⟨j,k⟩) = Sum.inl (Sum.inl ⟨j,k⟩) := by
  induction n generalizing s t with
  | zero => cases t <;> rfl
  | succ n ih =>
    cases t with
    | zero => rfl
    | succ t =>
      cases t with
      | zero => omega
      | succ t => exact ih history.2.2 t (by omega)

variable {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryActualActiveIds_ghost (t : ℕ) (he : t % 2 = 0) (j : J) (k : Fin (pads+1)) :
    markedMemoryActualActiveIds hZ history (t+1) j k = markedMemoryActualActiveIds hZ history t j k := by
  apply Subtype.ext
  change Sum.elim (markedMemoryLineageOrigin
    (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t)
    (fun b => Sum.inr ⟨t,b⟩) (markedMemoryHistoryTraceStep hZ history t (Sum.inl ⟨j,k⟩)) = _
  rw [markedMemoryHistoryTrace_active_even hZ history t he]
  rfl

theorem markedMemoryActualActive_ghost (t : ℕ) (he : t % 2 = 0) (j : J) (a : MarkedMemoryActualFiber hZ history j) :
    markedMemoryActualActive hZ history (t+1) j a ↔ markedMemoryActualActive hZ history t j a := by
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k,(markedMemoryActualActiveIds_ghost hZ history t he j k).symm.trans hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,(markedMemoryActualActiveIds_ghost hZ history t he j k).trans hk⟩

theorem markedMemoryActualActiveIds_alive (v : ℕ) (hv : v ≤ n) (j : J) (k : Fin (pads+1)) :
    markedMemoryActualFirst hZ history j (markedMemoryActualActiveIds hZ history (2*v) j k) ≤ 2*v ∧
      2*v+1 ≤ markedMemoryActualLast hZ history j (markedMemoryActualActiveIds hZ history (2*v) j k) := by
  have hfirst := markedMemoryLineageOrigin_birthTime_le
    (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) (2*v) (Sum.inl ⟨j,k⟩)
  have hid := congrArg Subtype.val (markedMemoryActualActiveIds_ghost hZ history (2*v) (by omega) j k)
  have hlife := (markedMemoryHistory_lifespan_exact hZ history
    (markedMemoryActualActiveIds hZ history (2*v) j k).1 (2*v+1)).mp ⟨by omega,Sum.inl ⟨j,k⟩,hid⟩
  exact ⟨hfirst,hlife.2⟩

def markedMemoryActualBirthQueue (t : ℕ) (j : J) : List (MarkedMemoryActualFiber hZ history j) :=
  (markedMemoryActualPendingQueue hZ history (t+1) j).filter
    (fun a => decide (markedMemoryActualFirst hZ history j a = t+1))

theorem markedMemoryActualBirthQueue_nodup (t : ℕ) (j : J) :
    (markedMemoryActualBirthQueue hZ history t j).Nodup :=
  (markedMemoryActualPendingQueue_nodup hZ history (t+1) j).filter _

theorem markedMemoryActualBirthQueue_mem (t : ℕ) (ht : t < 2*n+1) (he : t % 2 = 0) (j : J)
    (a : MarkedMemoryActualFiber hZ history j) :
    a ∈ markedMemoryActualBirthQueue hZ history t j ↔
      markedMemoryActualFirst hZ history j a = t+1 ∧ t+1 ≤ markedMemoryActualLast hZ history j a ∧
        ¬ markedMemoryActualActive hZ history t j a := by
  simp only [markedMemoryActualBirthQueue, List.mem_filter, decide_eq_true_eq,
    markedMemoryActualPendingQueue_interval hZ history (t+1) ht j a]
  have ha := markedMemoryActualActive_ghost hZ history t he j a
  constructor
  · rintro ⟨⟨_hf,hl,hn⟩,hb⟩
    exact ⟨hb,hl,fun h => hn (ha.mpr h)⟩
  · rintro ⟨hb,hl,hn⟩
    exact ⟨⟨hb.le,hl,fun h => hn (ha.mp h)⟩,hb⟩

end
end ArtinMatthews
