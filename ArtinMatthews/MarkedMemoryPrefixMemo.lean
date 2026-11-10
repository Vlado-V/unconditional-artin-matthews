module

public import ArtinMatthews.MarkedMemoryPotentialChronology
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! A chronological memo reads only the values born at its current
operation. Its exact prefix formula supplies the causal invariant for
the actual initial, ghost and edge birth updates. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} {M B n : ℕ}

def markedMemoryPotentialMemo
    (v : MarkedMemoryPotentialAddress J M B n → Option Nat.Primes) :
    ℕ → MarkedMemoryPotentialAddress J M B n → Option Nat.Primes
  | 0 => fun _ => none
  | t+1 => fun a => if markedMemoryPotentialChronologicalTime a=t then v a
      else markedMemoryPotentialMemo v t a

theorem markedMemoryPotentialMemo_eq
    (v : MarkedMemoryPotentialAddress J M B n → Option Nat.Primes) (t : ℕ)
    (a : MarkedMemoryPotentialAddress J M B n) :
    markedMemoryPotentialMemo v t a=
      if markedMemoryPotentialChronologicalTime a<t then v a else none := by
  induction t with
  | zero => simp [markedMemoryPotentialMemo]
  | succ t ih =>
    change (if markedMemoryPotentialChronologicalTime a=t then v a
      else markedMemoryPotentialMemo v t a)=_
    rw [ih]
    by_cases he : markedMemoryPotentialChronologicalTime a=t
    · simp [he]
    · by_cases hlt : markedMemoryPotentialChronologicalTime a<t
      · simp only [he,hlt,Nat.lt_succ_of_lt hlt,ite_false,ite_true]
      · have hge : ¬markedMemoryPotentialChronologicalTime a<t+1 := by omega
        simp only [he,hlt,hge,ite_false]

theorem markedMemoryPotentialMemo_prior
    (v : MarkedMemoryPotentialAddress J M B n → Option Nat.Primes) {t : ℕ}
    {a : MarkedMemoryPotentialAddress J M B n}
    (h : markedMemoryPotentialChronologicalTime a<t) :
    markedMemoryPotentialMemo v t a=v a := by
  rw [markedMemoryPotentialMemo_eq,ite_eq_left h]

theorem markedMemoryPotentialMemo_future
    (v : MarkedMemoryPotentialAddress J M B n → Option Nat.Primes) {t : ℕ}
    {a : MarkedMemoryPotentialAddress J M B n}
    (h : t ≤ markedMemoryPotentialChronologicalTime a) :
    markedMemoryPotentialMemo v t a=none := by
  rw [markedMemoryPotentialMemo_eq,ite_eq_right (not_lt.mpr h)]

theorem markedMemoryPotentialMemo_causal
    (v w : MarkedMemoryPotentialAddress J M B n → Option Nat.Primes) (t : ℕ)
    (h : ∀ a,markedMemoryPotentialChronologicalTime a<t → v a=w a) :
    markedMemoryPotentialMemo v t=markedMemoryPotentialMemo w t := by
  funext a
  simp only [markedMemoryPotentialMemo_eq]
  by_cases ha : markedMemoryPotentialChronologicalTime a<t
  · rw [ite_eq_left ha,ite_eq_left ha,h a ha]
  · rw [ite_eq_right ha,ite_eq_right ha]

def markedMemoryHistoryMemo
    [Fintype J] {P : J → Finset Nat.Primes} {pads : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    ℕ → MarkedMemoryPotentialAddress J (pads+1) B n → Option Nat.Primes :=
  markedMemoryPotentialMemo (markedMemoryPotentialAddressValue hZ history)

theorem markedMemoryHistoryMemo_eq
    [Fintype J] {P : J → Finset Nat.Primes} {pads : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (a : MarkedMemoryPotentialAddress J (pads+1) B n) :
    markedMemoryHistoryMemo hZ history t a=
      if markedMemoryPotentialChronologicalTime a<t then
        markedMemoryPotentialAddressValue hZ history a else none :=
  markedMemoryPotentialMemo_eq _ t a

end
end ArtinMatthews
