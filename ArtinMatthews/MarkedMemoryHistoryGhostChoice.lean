module

public import ArtinMatthews.MarkedMinorArcRawGhostAction
public import Mathlib.CategoryTheory.Category.Basic
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Choice-by-choice chronological coordinates for the actual ghost operator.
Deletion masks act on indexed old particles, and birth tuples remain ordered;
no distinctness of numeric prime or particle values is imposed here. -/
namespace ArtinMatthews
open scoped BigOperators

/-- A literal allowed ghost choice, with exactly its original dependent
birth-size and birth-label coordinates. -/
structure MarkedMemoryGhostChoice {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z) where
  deletion : MarkedRawGhostDeletion s.2.2
  allowed : MarkedRawGhostDeletionAllowed s.2.2 s.1.1 (hZ _ s.1.2) deletion
  sizes : MarkedRawGhostBirthSizes s.2.2 deletion
  births : MarkedRawGhostBirthLabels sizes

def markedMemoryGhostChoiceEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z) :
    MarkedMemoryGhostChoice hZ s ≃
      (Σ del : {d : MarkedRawGhostDeletion s.2.2 //
        MarkedRawGhostDeletionAllowed s.2.2 s.1.1 (hZ _ s.1.2) d},
        Σ l : MarkedRawGhostBirthSizes s.2.2 del.1, MarkedRawGhostBirthLabels l) where
  toFun choice := ⟨⟨choice.deletion,choice.allowed⟩,choice.sizes,choice.births⟩
  invFun choice := ⟨choice.1.1,choice.1.2,choice.2.1,choice.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance markedMemoryGhostChoice_fintype {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z) :
    Fintype (MarkedMemoryGhostChoice hZ s) := by
  classical
  exact Fintype.ofEquiv _ (markedMemoryGhostChoiceEquiv hZ s).symm

noncomputable def markedMemoryGhostChoiceTarget {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s) : MarkedRawState P M B Z :=
  markedRawGhostTargetState hZ s choice.deletion choice.sizes choice.births

/-- Signed coefficient times the actual tilted birth mass, including every
individual factorial. This does not identify the physical measure with nu. -/
noncomputable def markedMemoryGhostChoiceWeight {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s) : ℂ :=
  ((markedRawGhostSignedCoefficient V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) choice.deletion choice.sizes*
    markedRawGhostBirthMass ν choice.sizes choice.births : ℝ) : ℂ)

/-- Exact finite reindexing of the frozen signed ghost operation. No row
bound, convergence assertion or assumed history identity is used. -/
theorem markedMemoryGhostChoice_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (f : MarkedRawState P M B Z → ℂ)
    (s : MarkedRawState P M B Z) :
    (∑ choice : MarkedMemoryGhostChoice hZ s,
      markedMemoryGhostChoiceWeight ν V qStage ρ hZ s choice*
        f (markedMemoryGhostChoiceTarget hZ s choice)) =
      markedRawGhostApply ν V qStage ρ hZ f s := by
  classical
  rw [← Equiv.sum_comp (markedMemoryGhostChoiceEquiv hZ s).symm]
  simp only [Fintype.sum_sigma,markedMemoryGhostChoiceWeight,markedMemoryGhostChoiceTarget,
    markedMemoryGhostChoiceEquiv,Equiv.coe_fn_symm_mk]
  unfold markedRawGhostApply
  let g (del : MarkedRawGhostDeletion s.2.2) : ℂ :=
    ∑ l : MarkedRawGhostBirthSizes s.2.2 del, ∑ births : MarkedRawGhostBirthLabels l,
      ((markedRawGhostSignedCoefficient V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) del l*
        markedRawGhostBirthMass ν l births : ℝ) : ℂ)*f (markedRawGhostTargetState hZ s del l births)
  let allowed := MarkedRawGhostDeletionAllowed s.2.2 s.1.1 (hZ _ s.1.2)
  change (∑ del : {d // allowed d},g del.1)=∑ del,if allowed del then g del else 0
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter allowed) (by simp) g).symm

end ArtinMatthews
