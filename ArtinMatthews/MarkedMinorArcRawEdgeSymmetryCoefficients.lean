module

public import ArtinMatthews.MarkedMinorArcRawEdgeSymmetryTargets
public import ArtinMatthews.MarkedMinorArcRawEdgeAction
public import ArtinMatthews.MarkedMinorArcRawGhostSymmetryBoundary
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

/-! Literal edge prime-integration and geometric coefficients commute
with pending-index transport; every physical cutoff remains present. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews
set_option backward.isDefEq.respectTransparency false

/-- Each original fresh/promoted integration factor is expressed through
its actual target label and actual promotion flag, with no extra choice. -/
theorem markedRawEdgeChoicePrimeMass_eq_targetLast {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoicePrimeMass ν V hZ s c = ∏ j,
      if (c.promotions j).isSome then (V j)⁻¹
      else ν j (markedRawEdgeTargetLast s.2.2 c.promotions c.fresh j) := by
  unfold markedRawEdgeChoicePrimeMass
  apply Finset.prod_congr rfl
  intro j _
  split
  · rename_i hn
    have hi : (c.promotions j).isSome=false := by rw [hn]; rfl
    rw [hi]
    simp only [Bool.false_eq_true, ite_false]
    unfold markedRawEdgeTargetLast
    split
    · rfl
    · rename_i k hk
      rw [hn] at hk
      cases hk
  · rename_i k hk
    have hi : (c.promotions j).isSome=true := by rw [hk]; rfl
    simp only [hi, ite_true]

theorem markedRawEdgeChoicePrimeMass_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (a : MarkedRawActive P (pads+1))
    (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (c : MarkedRawEdgeChoice hZ (z,(a,m))) :
    markedRawEdgeChoicePrimeMass ν V hZ (z,(a,markedRawMemoryPermute m σ))
      (markedRawEdgeChoicePermute hZ z a m σ c) =
      markedRawEdgeChoicePrimeMass ν V hZ (z,(a,m)) c := by
  rw [markedRawEdgeChoicePrimeMass_eq_targetLast, markedRawEdgeChoicePrimeMass_eq_targetLast]
  have hl := markedRawEdgeChoicePermute_targetLast hZ z a m σ c
  rw [hl]
  apply Finset.prod_congr rfl
  intro j _
  have hi : ((markedRawEdgeChoicePermute hZ z a m σ c).promotions j).isSome=
      (c.promotions j).isSome := by
    change ((c.promotions j).map (σ j).symm).isSome=(c.promotions j).isSome
    simp
  rw [hi]

theorem markedRawEdgeChoiceCoefficient_permute {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (hχ : ∀ z a, MarkedRawMemorySymmetric (fun m => χ (z,(a,m))))
    (z : Z) (a : MarkedRawActive P (pads+1)) (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) (c : MarkedRawEdgeChoice hZ (z,(a,m))) :
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ (z,(a,markedRawMemoryPermute m σ))
      (markedRawEdgeChoicePermute hZ z a m σ c) =
      markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ (z,(a,m)) c := by
  classical
  have hl := markedRawEdgeChoicePermute_targetLast hZ z a m σ c
  have hs : markedRawEndpointFactor hZ 1 χ (z,(a,markedRawMemoryPermute m σ))=
      markedRawEndpointFactor hZ 1 χ (z,(a,m)) :=
    markedRawEndpointFactor_symmetric hZ 1 χ hχ z a m σ
  have ht := markedRawEdgeTargetState_symmetric_permute hZ z a m σ
    (markedRawEndpointFactor hZ 1 χ) (markedRawEndpointFactor_symmetric hZ 1 χ hχ) c
  have hh := markedRawEdgeTargetMemory_pendingHits_permute hZ z a m σ c
    c.target.1 (hZ _ c.target.2)
  have hp : (markedRawEdgeChoicePermute hZ z a m σ c).target=c.target := rfl
  unfold markedRawEdgeChoiceCoefficient
  dsimp only
  rw [hl, markedRawPendingHits_permute, hs, ht]
  dsimp only [markedRawEdgeTargetState]
  simp only [hp, hh]

end ArtinMatthews
