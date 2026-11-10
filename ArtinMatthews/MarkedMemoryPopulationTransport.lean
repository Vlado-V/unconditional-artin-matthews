module

public import ArtinMatthews.MarkedMemoryHistoryEdgeOriginsPopulation
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

/-! Constructor formulas for population transport along an exact raw
state equality. Active slots keep their indices; pending slots use only
the induced equality of the corresponding memory lengths. -/
namespace ArtinMatthews

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {M B : ℕ} {Z : Finset (ℤ × ℤ)} {s t : MarkedRawState P M B Z}

def markedMemoryPopulationStateCast (h : s = t) : MarkedMemoryPopulationIndex s ≃ MarkedMemoryPopulationIndex t :=
  Equiv.cast (congrArg MarkedMemoryPopulationIndex h)

theorem markedMemoryPopulationStateCast_active (h : s = t) (j : J) (k : Fin M) :
    markedMemoryPopulationStateCast h (Sum.inl ⟨j,k⟩) = Sum.inl ⟨j,k⟩ := by
  cases h
  rfl

theorem markedMemoryPopulationStateCast_pending (h : s = t) (j : J) (k : Fin (s.2.2.1.1 j : ℕ)) :
    markedMemoryPopulationStateCast h (Sum.inr ⟨j,k⟩) =
      Sum.inr ⟨j,Fin.cast (congrArg (fun r : MarkedRawState P M B Z => (r.2.2.1.1 j : ℕ)) h) k⟩ := by
  cases h
  rfl

theorem markedMemoryPopulationStateCast_refl (i : MarkedMemoryPopulationIndex s) :
    markedMemoryPopulationStateCast (rfl : s = s) i = i := rfl

theorem markedMemoryPopulationStateCast_prime (h : s = t) (i : MarkedMemoryPopulationIndex s) :
    markedMemoryPopulationPrime t (markedMemoryPopulationStateCast h i) = markedMemoryPopulationPrime s i := by
  cases h
  rfl

theorem markedMemoryPopulationStateCast_trans {r : MarkedRawState P M B Z}
    (h₁ : s = t) (h₂ : t = r) (i : MarkedMemoryPopulationIndex s) :
    markedMemoryPopulationStateCast h₂ (markedMemoryPopulationStateCast h₁ i) =
      markedMemoryPopulationStateCast (h₁.trans h₂) i := by
  cases h₁
  cases h₂
  rfl

end ArtinMatthews
