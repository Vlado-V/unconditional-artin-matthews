module

public import ArtinMatthews.MarkedMinorArcRawGhostBirthModifier
public import ArtinMatthews.MarkedMinorArcRawEdgeBirthModifier
public import ArtinMatthews.MarkedBirthLocalPhases
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

/-! The actual local circle phases are old-memory equivariant birth
modifiers. Their performed flags remain literal, including unperformed
ordered ghost indices and promoted edge slots. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryGhostBirthPhase {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B n : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (θ : MarkedMemoryPotentialAddress J M B n → AddCircle (1:ℝ)) (t : Fin (n+1))
    (l : J → Fin (B+1)) (births : (j : J) → Fin (l j:ℕ) → ↥(P j)) : ℂ :=
  ∏ j, ∏ k : Fin B, markedBirthLocalMultiplier σ θ (Sum.inr (Sum.inl (t,(j,k))))
    (if hk : k.1 < (l j:ℕ) then some ((births j ⟨k.1,hk⟩).1) else none)

def markedMemoryEdgeBirthPhase {J : Type*} [Fintype J] [DecidableEq J] {M B n : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (θ : MarkedMemoryPotentialAddress J M B n → AddCircle (1:ℝ)) (t : Fin n)
    (j : J) (p : Option Nat.Primes) : ℂ :=
  markedBirthLocalMultiplier σ θ (Sum.inr (Sum.inr (t,j))) p

theorem markedMemoryGhostBirthPhase_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B n : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (θ : MarkedMemoryPotentialAddress J M B n → AddCircle (1:ℝ)) (t : Fin (n+1))
    (l : J → Fin (B+1)) (births : (j : J) → Fin (l j:ℕ) → ↥(P j)) :
    ‖markedMemoryGhostBirthPhase σ θ t l births‖ ≤ 1 := by
  unfold markedMemoryGhostBirthPhase
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun j _ => norm_nonneg _)
  intro j _
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun k _ => norm_nonneg _)
    (fun k _ => markedBirthLocalMultiplier_norm_le σ θ _ _)

theorem markedMemoryEdgeBirthPhase_norm_le {J : Type*} [Fintype J] [DecidableEq J] {M B n : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (θ : MarkedMemoryPotentialAddress J M B n → AddCircle (1:ℝ)) (t : Fin n)
    (j : J) (p : Option Nat.Primes) : ‖markedMemoryEdgeBirthPhase σ θ t j p‖ ≤ 1 :=
  markedBirthLocalMultiplier_norm_le σ θ _ _

theorem markedMemoryGhostBirthPhase_choice {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B n : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P M B Z}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (θ : MarkedMemoryPotentialAddress J M B n → AddCircle (1:ℝ)) (t : Fin (n+1))
    (c : MarkedMemoryGhostChoice hZ s) :
    markedMemoryGhostBirthPhase σ θ t c.sizes.1 c.births =
      ∏ j, ∏ k : Fin B, markedBirthLocalMultiplier σ θ (Sum.inr (Sum.inl (t,(j,k))))
        (markedMemoryGhostPotentialValue c j k) := rfl

theorem markedMemoryEdgeBirthPhase_choice {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P (pads+1) B Z}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B n → AddCircle (1:ℝ)) (t : Fin n)
    (c : MarkedMemoryEdgeChoice hZ s) :
    markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhase σ θ t) (markedRawSlotEquiv c.1 s) c.2.1 =
      ∏ j, markedBirthLocalMultiplier σ θ (Sum.inr (Sum.inr (t,j)))
        (markedMemoryEdgePotentialValue c j) := rfl

theorem markedMemoryGhostBirthPhase_eq_one {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B n : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (θ : MarkedMemoryPotentialAddress J M B n → AddCircle (1:ℝ)) (t : Fin (n+1))
    (ht : some (2*t.1) ∉ σ.support.image markedMemoryPotentialOperation)
    (l : J → Fin (B+1)) (births : (j : J) → Fin (l j:ℕ) → ↥(P j)) :
    markedMemoryGhostBirthPhase σ θ t l births = 1 := by
  apply Finset.prod_eq_one
  intro j _
  apply Finset.prod_eq_one
  intro k _
  exact markedBirthLocalMultiplier_unmodified markedMemoryPotentialOperation σ θ _ ht _ rfl _

theorem markedMemoryEdgeBirthPhase_eq_one {J : Type*} [Fintype J] [DecidableEq J] {M B n : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (θ : MarkedMemoryPotentialAddress J M B n → AddCircle (1:ℝ)) (t : Fin n)
    (ht : some (2*t.1+1) ∉ σ.support.image markedMemoryPotentialOperation)
    (j : J) (p : Option Nat.Primes) : markedMemoryEdgeBirthPhase σ θ t j p = 1 :=
  markedBirthLocalMultiplier_unmodified markedMemoryPotentialOperation σ θ _ ht _ rfl _

theorem markedMemoryGhostBirthPhaseApply_symmetric
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ) {M B n : ℕ}
    {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (θ : MarkedMemoryPotentialAddress J M B n → AddCircle (1:ℝ)) (t : Fin (n+1))
    (f : MarkedRawState P M B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (z : Z) (a : MarkedRawActive P M) :
    MarkedRawMemorySymmetric (fun m => markedRawGhostBirthModifiedApply ν V qStage ρ hZ
      (markedMemoryGhostBirthPhase σ θ t) f (z,(a,m))) :=
  markedRawGhostBirthModifiedApply_symmetric ν V qStage ρ hZ _ f hf z a

end ArtinMatthews
