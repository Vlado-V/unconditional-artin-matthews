module

public import ArtinMatthews.MarkedRawBoundary
public import ArtinMatthews.MarkedMinorArcRawShiftGeometry
public import ArtinMatthews.MarkedMinorArcRawGhostAction
public import ArtinMatthews.MarkedMinorArcRawMemoryAmbient
public import ArtinMatthews.MarkedMinorArcRawGhostSymmetry
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

/-! The literal empty-memory boundary and physical endpoint cutoffs belong
to the actual symmetric-pending domain used by the ghost operator. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem markedRawMemory_eq_empty_of_sizes {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (h : m.1=(markedRawBoundaryEmptyMemory P B).1) : m=markedRawBoundaryEmptyMemory P B := by
  rcases m with ⟨k,a⟩
  dsimp only at h
  subst k
  congr 1
  funext j i
  exact Fin.elim0 i

theorem markedRawMemoryPermute_empty_iff {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) :
    markedRawMemoryPermute m σ=markedRawBoundaryEmptyMemory P B ↔ m=markedRawBoundaryEmptyMemory P B := by
  constructor
  · intro h
    have hh := congrArg (fun t : MarkedRawMemory P B => t.1) h
    exact markedRawMemory_eq_empty_of_sizes m hh
  · intro h
    have hh := congrArg (fun t : MarkedRawMemory P B => t.1) h
    apply markedRawMemory_eq_empty_of_sizes
    exact hh

theorem markedRawBoundary_symmetric {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (z₀ z : Z) (a : MarkedRawActive P M) :
    MarkedRawMemorySymmetric (fun m : MarkedRawMemory P B => markedRawBoundary z₀ (z,(a,m))) := by
  classical
  intro m σ
  unfold markedRawBoundary
  change (if z=z₀ ∧ markedRawMemoryPermute m σ=markedRawBoundaryEmptyMemory P B then (1:ℂ) else 0)=
    (if z=z₀ ∧ m=markedRawBoundaryEmptyMemory P B then (1:ℂ) else 0)
  simp only [markedRawMemoryPermute_empty_iff]

theorem markedRawGhostApply_boundary_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (z₀ z : Z) (a : MarkedRawActive P M) :
    MarkedRawMemorySymmetric (fun m : MarkedRawMemory P B =>
      markedRawGhostApply ν V qStage ρ hZ (markedRawBoundary z₀) (z,(a,m))) :=
  markedRawGhostApply_symmetric ν V qStage ρ hZ (markedRawBoundary z₀)
    (markedRawBoundary_symmetric z₀) z a

/-- Physical multipliers that depend only on position and active lists
are automatically in the genuine pending-symmetric domain. -/
theorem markedRawMemoryIndependent_symmetric {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (χ : Z → MarkedRawActive P M → ℂ) (z : Z) (a : MarkedRawActive P M) :
    MarkedRawMemorySymmetric (fun _m : MarkedRawMemory P B => χ z a) := fun _ _ => rfl

theorem markedRawEndpointFactor_symmetric {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ρ : ℝ) (χ : MarkedRawState P M B Z → ℂ)
    (hχ : ∀ z a, MarkedRawMemorySymmetric (fun m => χ (z,(a,m))))
    (z : Z) (a : MarkedRawActive P M) :
    MarkedRawMemorySymmetric (fun m => markedRawEndpointFactor hZ ρ χ (z,(a,m))) := by
  classical
  intro m σ
  unfold markedRawEndpointFactor
  change (if MarkedRawActiveDistinct a then
    ((ρ^markedRawPendingHits (markedRawMemoryPermute m σ) z.1 (hZ _ z.2) : ℝ) : ℂ)*
      χ (z,(a,markedRawMemoryPermute m σ)) else 0) = _
  have hh : χ (z,(a,markedRawMemoryPermute m σ))=χ (z,(a,m)) := hχ z a m σ
  rw [markedRawPendingHits_permute, hh]

theorem markedRawFirstGood_permute {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (z : Z) (a : MarkedRawActive P M)
    (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) :
    MarkedRawFirstGood r d₀ Y w (z,(a,markedRawMemoryPermute m σ)) ↔
      MarkedRawFirstGood r d₀ Y w (z,(a,m)) := Iff.rfl

theorem markedRawFirstGoodCutoff_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (χ : MarkedRawState P M B Z → ℂ)
    (hχ : ∀ z a, MarkedRawMemorySymmetric (fun m => χ (z,(a,m))))
    (z : Z) (a : MarkedRawActive P M) :
    MarkedRawMemorySymmetric (fun m => markedRawFirstGoodCutoff r d₀ Y w χ (z,(a,m))) := by
  classical
  intro m σ
  unfold markedRawFirstGoodCutoff
  change (if MarkedRawFirstGood r d₀ Y w (z,(a,markedRawMemoryPermute m σ)) then
    χ (z,(a,markedRawMemoryPermute m σ)) else 0)=_
  have hh : χ (z,(a,markedRawMemoryPermute m σ))=χ (z,(a,m)) := hχ z a m σ
  rw [markedRawFirstGood_permute, hh]

end ArtinMatthews
