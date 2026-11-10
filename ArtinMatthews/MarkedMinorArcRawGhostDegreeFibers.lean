module

public import ArtinMatthews.MarkedMinorArcRawGhostDegreeChoices
public import ArtinMatthews.MarkedMinorArcRawGhostAction
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

/-! The literal particle and birth fibers over the finite degree reindexing.
Eligibility remains the exact old-hit condition; repetitions remain allowed. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev MarkedRawGhostMemoryChoice {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (B : ℕ) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :=
  Σ m : MarkedRawMemory P B,
    Σ del : {d : MarkedRawGhostDeletion m // MarkedRawGhostDeletionAllowed m z hz d},
      Σ l : MarkedRawGhostBirthSizes m del.1, MarkedRawGhostBirthLabels l

abbrev MarkedRawGhostShapePayload {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostShape J B) :=
  {data : ((j : J) → Fin (a.1.1 j:ℕ) → MarkedRawParticle (P j)) ×
      ((j : J) → Fin (a.2.2.1 j:ℕ) → ↥(P j)) //
    MarkedRawGhostDeletionAllowed ⟨a.1,data.1⟩ z hz a.2.1}

abbrev MarkedRawGhostDegreePayload {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B) :=
  MarkedRawGhostShapePayload P z hz (markedRawGhostDegreeShapeToShape a)

def markedRawGhostShapeMemoryChoiceEquiv {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    (Σ a : MarkedRawGhostShape J B, MarkedRawGhostShapePayload P z hz a) ≃
      MarkedRawGhostMemoryChoice P B z hz where
  toFun a := ⟨⟨a.1.1,a.2.1.1⟩,⟨a.1.2.1,a.2.2⟩,a.1.2.2,a.2.1.2⟩
  invFun a := ⟨⟨a.1.1,a.2.1.1,a.2.2.1⟩,⟨⟨a.1.2,a.2.2.2⟩,a.2.1.2⟩⟩
  left_inv := by rintro ⟨⟨k,del,l⟩,⟨⟨old,births⟩,ha⟩⟩; rfl
  right_inv := by rintro ⟨⟨k,old⟩,⟨del,ha⟩,l,births⟩; rfl

def markedRawGhostDegreeMemoryChoiceEquiv {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    (Σ a : MarkedRawGhostDegreeShape J B, MarkedRawGhostDegreePayload P z hz a) ≃
      MarkedRawGhostMemoryChoice P B z hz :=
  (Equiv.sigmaCongr markedRawGhostDegreeShapeEquiv (fun _ => Equiv.refl _)).trans
    (markedRawGhostShapeMemoryChoiceEquiv P z hz)

def markedRawGhostDegreeMemoryChoice {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B) (data : MarkedRawGhostDegreePayload P z hz a) :
    MarkedRawGhostMemoryChoice P B z hz :=
  markedRawGhostShapeMemoryChoiceEquiv P z hz ⟨markedRawGhostDegreeShapeToShape a,data⟩

theorem markedRawGhostDegreeMemoryChoiceEquiv_apply {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B) (data : MarkedRawGhostDegreePayload P z hz a) :
    markedRawGhostDegreeMemoryChoiceEquiv P z hz ⟨a,data⟩=
      markedRawGhostDegreeMemoryChoice P z hz a data := rfl

theorem markedRawGhost_memory_degree_sum {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    {T : Type*} [AddCommMonoid T] (f : MarkedRawGhostMemoryChoice P B z hz → T) :
    (∑ m : MarkedRawMemory P B,
      ∑ del : {d : MarkedRawGhostDeletion m // MarkedRawGhostDeletionAllowed m z hz d},
        ∑ l : MarkedRawGhostBirthSizes m del.1, ∑ births : MarkedRawGhostBirthLabels l,
          f ⟨m,del,l,births⟩) =
      ∑ a : MarkedRawGhostDegreeShape J B, ∑ data : MarkedRawGhostDegreePayload P z hz a,
        f (markedRawGhostDegreeMemoryChoice P z hz a data) := by
  classical
  simpa only [Fintype.sum_sigma,markedRawGhostDegreeMemoryChoiceEquiv_apply] using
    (Equiv.sum_comp (markedRawGhostDegreeMemoryChoiceEquiv P z hz) f).symm

theorem markedRawGhost_degree_source_mass {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℝ) {B : ℕ}
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (a : MarkedRawGhostDegreeShape J B)
    (data : MarkedRawGhostDegreePayload P z hz a) :
    markedRawMemoryMass ν (markedRawGhostDegreeMemoryChoice P z hz a data).1 =
      ∏ j, (∏ i, ν j (data.1.1 j i).1)/(Nat.factorial (a.1.survivors j+a.1.deleted j):ℝ) := rfl

theorem markedRawGhost_degree_birth_mass {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℝ) {B : ℕ}
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (a : MarkedRawGhostDegreeShape J B)
    (data : MarkedRawGhostDegreePayload P z hz a) :
    markedRawGhostBirthMass ν (markedRawGhostDegreeMemoryChoice P z hz a data).2.2.1
      (markedRawGhostDegreeMemoryChoice P z hz a data).2.2.2 =
      ∏ j, (∏ i, ν j (data.1.2 j i))/(Nat.factorial (a.1.born j):ℝ) := rfl

end
end ArtinMatthews
