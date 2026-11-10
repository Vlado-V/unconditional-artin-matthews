module

public import ArtinMatthews.MarkedMemoryHistoryPrimewiseCRT
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact coefficient-weighted CRT substitution for the actual finite
chronological history sum. It keeps arbitrary additional tests and the
explicit global birth-distinct restriction. No identity with a separate
lifespan sum or physical/tilted measure is assumed. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B n S : ℕ} [NeZero S]
  {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
  (ν : (band : J) → ↥(P band) → ℝ) (V : J → ℝ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
  {s : MarkedRawState P (pads+1) B Z}

theorem markedMemoryHistoryCRT_weighted_sum
    (qStage : ℕ → ℝ) (j : ℕ) (hS : Squarefree S)
    (hempty : ∀ band, (s.2.2.1.1 band : ℕ) = 0) (q : ℝ)
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (∑ history : MarkedMemoryChronologicalHistory hZ n s,
      if keep history ∧ MarkedMemoryHistoryBirthDistinct hZ history then
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history *
          markedMemoryHistoryCRTAverage hZ history hS q * f history else 0) =
    ∑ history : MarkedMemoryChronologicalHistory hZ n s,
      if keep history ∧ MarkedMemoryHistoryBirthDistinct hZ history then
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history *
          markedMemoryHistoryCRTExpansion (S := S) hZ history q * f history else 0 := by
  apply Finset.sum_congr rfl
  intro history _
  by_cases hk : keep history ∧ MarkedMemoryHistoryBirthDistinct hZ history
  · rw [ite_eq_left hk, ite_eq_left hk]
    exact congrArg (fun z : ℂ => z * f history)
      (markedMemoryHistoryCRT_weighted_expansion hZ history ν V ψ η d₀ Y Q ρ qStage χ j
        hS hempty hk.2 q)
  · rw [ite_eq_right hk, ite_eq_right hk]

/-- The finite root average may be taken outside the complete actual
history sum, preserving its literal coefficients and additional tests. -/
theorem markedMemoryHistoryCRT_average_sum
    (qStage : ℕ → ℝ) (j : ℕ) (hS : Squarefree S)
    (hempty : ∀ band, (s.2.2.1.1 band : ℕ) = 0) (q : ℝ)
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℂ)⁻¹ *
      (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
        ∑ history : MarkedMemoryChronologicalHistory hZ n s,
          if keep history ∧ MarkedMemoryHistoryBirthDistinct hZ history then
            markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history *
              markedMemoryHistoryCRTRootTest hZ history hS q g * f history else 0) =
    ∑ history : MarkedMemoryChronologicalHistory hZ n s,
      if keep history ∧ MarkedMemoryHistoryBirthDistinct hZ history then
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history *
          markedMemoryHistoryCRTExpansion (S := S) hZ history q * f history else 0 := by
  calc
    _ = ∑ history : MarkedMemoryChronologicalHistory hZ n s,
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℂ)⁻¹ *
          ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
            if keep history ∧ MarkedMemoryHistoryBirthDistinct hZ history then
              markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history *
                markedMemoryHistoryCRTRootTest hZ history hS q g * f history else 0 := by
      rw [Finset.sum_comm, Finset.mul_sum]
    _ = ∑ history : MarkedMemoryChronologicalHistory hZ n s,
        if keep history ∧ MarkedMemoryHistoryBirthDistinct hZ history then
          markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history *
            markedMemoryHistoryCRTAverage hZ history hS q * f history else 0 := by
      apply Finset.sum_congr rfl
      intro history _
      by_cases hk : keep history ∧ MarkedMemoryHistoryBirthDistinct hZ history
      · simp only [ite_eq_left hk]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        unfold markedMemoryHistoryCRTAverage
        ring
      · simp only [ite_eq_right hk, Finset.sum_const_zero, mul_zero]
    _ = _ := markedMemoryHistoryCRT_weighted_sum hZ ν V ψ η d₀ Y Q ρ χ
      qStage j hS hempty q keep f

/-- The actual square-root endpoint q schedule, with all n+1 original
vertices and the literal chronological coefficient at initial stage zero. -/
theorem markedMemoryHistoryCRT_source_weighted_expansion
    (history : MarkedMemoryChronologicalHistory hZ n s) (hS : Squarefree S)
    (hempty : ∀ band, (s.2.2.1.1 band : ℕ) = 0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history) (q : ℝ) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ
        (markedMemoryHistoryVisitSchedule q n) χ n 0 history *
      markedMemoryHistoryCRTAverage hZ history hS q =
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ
        (markedMemoryHistoryVisitSchedule q n) χ n 0 history *
      markedMemoryHistoryCRTExpansion (S := S) hZ history q :=
  markedMemoryHistoryCRT_weighted_expansion hZ history ν V ψ η d₀ Y Q ρ
    (markedMemoryHistoryVisitSchedule q n) χ 0 hS hempty hd q

theorem markedMemoryHistoryCRT_source_weighted_sum
    (hS : Squarefree S) (hempty : ∀ band, (s.2.2.1.1 band : ℕ) = 0) (q : ℝ)
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (∑ history : MarkedMemoryChronologicalHistory hZ n s,
      if keep history ∧ MarkedMemoryHistoryBirthDistinct hZ history then
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ
            (markedMemoryHistoryVisitSchedule q n) χ n 0 history *
          markedMemoryHistoryCRTAverage hZ history hS q * f history else 0) =
    ∑ history : MarkedMemoryChronologicalHistory hZ n s,
      if keep history ∧ MarkedMemoryHistoryBirthDistinct hZ history then
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ
            (markedMemoryHistoryVisitSchedule q n) χ n 0 history *
          markedMemoryHistoryCRTExpansion (S := S) hZ history q * f history else 0 :=
  markedMemoryHistoryCRT_weighted_sum hZ ν V ψ η d₀ Y Q ρ χ
    (markedMemoryHistoryVisitSchedule q n) 0 hS hempty q keep f

theorem markedMemoryHistoryCRT_source_average_sum
    (hS : Squarefree S) (hempty : ∀ band, (s.2.2.1.1 band : ℕ) = 0) (q : ℝ)
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℂ)⁻¹ *
      (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
        ∑ history : MarkedMemoryChronologicalHistory hZ n s,
          if keep history ∧ MarkedMemoryHistoryBirthDistinct hZ history then
            markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ
                (markedMemoryHistoryVisitSchedule q n) χ n 0 history *
              markedMemoryHistoryCRTRootTest hZ history hS q g * f history else 0) =
    ∑ history : MarkedMemoryChronologicalHistory hZ n s,
      if keep history ∧ MarkedMemoryHistoryBirthDistinct hZ history then
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ
            (markedMemoryHistoryVisitSchedule q n) χ n 0 history *
          markedMemoryHistoryCRTExpansion (S := S) hZ history q * f history else 0 :=
  markedMemoryHistoryCRT_average_sum hZ ν V ψ η d₀ Y Q ρ χ
    (markedMemoryHistoryVisitSchedule q n) 0 hS hempty q keep f

end
end ArtinMatthews
