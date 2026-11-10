module

public import ArtinMatthews.MarkedMinorArcRawEdgeModifier
public import ArtinMatthews.MarkedMemoryPotentialBirths
public import ArtinMatthews.MarkedMinorArcRawEdgeSymmetryTargets
public import ArtinMatthews.MarkedMinorArcRawEdgeSymmetryCoefficients
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

/-! Literal fresh-slot birth phases do not inspect old promotion indices.
Their performed flag and target prime are preserved by the actual pending
index transport, so the modified edge preserves the symmetric domain. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawEdgeBirthValue {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) (j : J) : Option Nat.Primes :=
  if c.promotions j = none then some ((markedRawEdgeTargetLast s.2.2 c.promotions c.fresh j).1)
  else none

theorem markedMemoryEdgePotentialValue_eq_raw {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P (pads+1) B Z}
    (c : MarkedMemoryEdgeChoice hZ s) (j : J) :
    markedMemoryEdgePotentialValue c j = markedRawEdgeBirthValue (markedRawSlotEquiv c.1 s) c.2.1 j := rfl

def markedRawEdgeBirthModifier {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} (φ : J → Option Nat.Primes → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) : ℂ :=
  ∏ j, φ j (markedRawEdgeBirthValue s c j)

theorem markedRawEdgeBirthModifier_norm_le {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} (φ : J → Option Nat.Primes → ℂ)
    (hφ : ∀ j p, ‖φ j p‖ ≤ 1) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) : ‖markedRawEdgeBirthModifier φ s c‖ ≤ 1 := by
  unfold markedRawEdgeBirthModifier
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun j _ => norm_nonneg _) (fun j _ => hφ j _)

set_option backward.isDefEq.respectTransparency false in
theorem markedRawEdgeBirthValue_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (a : MarkedRawActive P (pads+1))
    (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j:ℕ)))
    (c : MarkedRawEdgeChoice hZ (z,(a,m))) (j : J) :
    markedRawEdgeBirthValue (z,(a,markedRawMemoryPermute m σ))
      (markedRawEdgeChoicePermute hZ z a m σ c) j = markedRawEdgeBirthValue (z,(a,m)) c j := by
  have hf : (markedRawEdgeChoicePermute hZ z a m σ c).promotions j = none ↔ c.promotions j = none := by
    change (c.promotions j).map (σ j).symm = none ↔ c.promotions j = none
    simp
  have hl := markedRawEdgeChoicePermute_targetLast hZ z a m σ c
  unfold markedRawEdgeBirthValue
  by_cases hj : c.promotions j = none
  · rw [ite_eq_left (hf.mpr hj),ite_eq_left hj,hl]
  · rw [ite_eq_right (fun h => hj (hf.mp h)),ite_eq_right hj]

theorem markedRawEdgeBirthModifier_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (φ : J → Option Nat.Primes → ℂ)
    (z : Z) (a : MarkedRawActive P (pads+1)) (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j:ℕ))) (c : MarkedRawEdgeChoice hZ (z,(a,m))) :
    markedRawEdgeBirthModifier φ (z,(a,markedRawMemoryPermute m σ))
      (markedRawEdgeChoicePermute hZ z a m σ c) = markedRawEdgeBirthModifier φ (z,(a,m)) c := by
  unfold markedRawEdgeBirthModifier
  apply Finset.prod_congr rfl
  intro j _
  rw [markedRawEdgeBirthValue_permute]

theorem markedRawEdgeBirthModifiedApply_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ) (φ : J → Option Nat.Primes → ℂ)
    (hχ : ∀ z a, MarkedRawMemorySymmetric (fun m => χ (z,(a,m))))
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (z : Z) (a : MarkedRawActive P (pads+1)) :
    MarkedRawMemorySymmetric (fun m => markedRawEdgeModifiedApply ν V hZ ψ η d₀ Y Q ρ χ
      (markedRawEdgeBirthModifier φ) f (z,(a,m))) := by
  classical
  intro m σ
  unfold markedRawEdgeModifiedApply
  dsimp only
  rw [← Equiv.sum_comp (markedRawEdgeChoicePermute hZ z a m σ)]
  apply Finset.sum_congr rfl
  intro c _
  rw [markedRawEdgeChoicePrimeMass_permute,
    markedRawEdgeChoiceCoefficient_permute hZ ψ η d₀ Y Q ρ χ hχ,
    markedRawEdgeTargetState_symmetric_permute hZ z a m σ f hf,
    markedRawEdgeBirthModifier_permute]

end ArtinMatthews
