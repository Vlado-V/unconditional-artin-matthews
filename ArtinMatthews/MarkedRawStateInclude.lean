module

public import ArtinMatthews.MarkedRawBoundary
public import ArtinMatthews.MarkedMinorArcRawSlotAverage
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

/-! Exact inclusion of a finite position window. Active labels and every
indexed pending particle are unchanged, so the original state mass,
boundary and slot permutations commute with the inclusion. -/

noncomputable section
namespace ArtinMatthews

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {M B : ℕ} {Z W : Finset (ℤ × ℤ)} (h : Z ⊆ W)

def markedRawStateInclude (s : MarkedRawState P M B Z) : MarkedRawState P M B W :=
  (⟨s.1.1,h s.1.2⟩,s.2)

def markedRawStateWindowEquiv : MarkedRawState P M B Z ≃
    {s : MarkedRawState P M B W // s.1.1 ∈ Z} where
  toFun s := ⟨markedRawStateInclude h s,s.1.2⟩
  invFun s := (⟨s.1.1.1,s.2⟩,s.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem markedRawStateInclude_injective :
    Function.Injective (markedRawStateInclude (P := P) (M := M) (B := B) h) := by
  intro s t he
  have hs := congrArg (fun u : MarkedRawState P M B W => u.1.1) he
  have ht := congrArg (fun u : MarkedRawState P M B W => u.2) he
  exact Prod.ext (Subtype.ext hs) ht

theorem markedRawStateInclude_mass (ν : (j : J) → ↥(P j) → ℝ)
    (s : MarkedRawState P M B Z) :
    markedRawStateMass ν (markedRawStateInclude h s)=markedRawStateMass ν s := rfl

theorem markedRawStateInclude_boundary (z₀ : Z) (s : MarkedRawState P M B Z) :
    markedRawBoundary (⟨z₀.1,h z₀.2⟩ : W) (markedRawStateInclude h s)=markedRawBoundary z₀ s := by
  classical
  simp only [markedRawBoundary,markedRawStateInclude,Subtype.ext_iff]

theorem markedRawStateInclude_slots (s : MarkedRawState P M B Z)
    (σ : J → Equiv.Perm (Fin M)) :
    markedRawStateInclude h (markedRawSlotEquiv σ s)=
      markedRawSlotEquiv σ (markedRawStateInclude h s) := rfl

end ArtinMatthews
