module

public import ArtinMatthews.MarkedMemoryHistoryOrigins
public import ArtinMatthews.MarkedMinorArcRawMemoryAmbient
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

/-! Actual birth-index permutations extend by the identity on surviving old indices.
All identities remain valid when old and new numeric particle values repeat. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

/-- Reindex the actual birth slots, preserving every assigned numeric prime and its multiplicity. -/
def markedMemoryGhostBirthPermute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
    {del : MarkedRawGhostDeletion m} (l : MarkedRawGhostBirthSizes m del)
    (births : MarkedRawGhostBirthLabels l)
    (π : (j : J) → Equiv.Perm (Fin (l.1 j : ℕ))) : MarkedRawGhostBirthLabels l :=
  fun j i => births j (π j i)

/-- The exact permutation of target memory: identity on old survivors and π on new slots. -/
def markedMemoryGhostBirthIndexPerm {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del)
    (π : (j : J) → Equiv.Perm (Fin (l.1 j : ℕ))) (j : J) :
    Equiv.Perm (Fin ((markedRawGhostTargetSizes m del l).1 j : ℕ)) :=
  (markedMemoryGhostOrigin m del l j).trans
    ((Equiv.sumCongr (Equiv.refl _) (π j)).trans (markedMemoryGhostOrigin m del l j).symm)

/-- Literal survivor-then-birth memory is equivariant under the actual indexed permutation. -/
theorem markedMemoryGhostTargetMemory_birth_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l)
    (π : (j : J) → Equiv.Perm (Fin (l.1 j : ℕ))) :
    markedRawGhostTargetMemory m z hz del l (markedMemoryGhostBirthPermute l births π) =
      markedRawMemoryPermute (markedRawGhostTargetMemory m z hz del l births)
        (markedMemoryGhostBirthIndexPerm m del l π) := by
  apply Sigma.ext (x := markedRawGhostTargetMemory m z hz del l
    (markedMemoryGhostBirthPermute l births π))
    (y := markedRawMemoryPermute (markedRawGhostTargetMemory m z hz del l births)
      (markedMemoryGhostBirthIndexPerm m del l π)) rfl
  apply heq_of_eq
  funext j i
  change (markedRawGhostTargetMemory m z hz del l
      (markedMemoryGhostBirthPermute l births π)).2 j i =
    (markedRawGhostTargetMemory m z hz del l births).2 j
      (markedMemoryGhostBirthIndexPerm m del l π j i)
  obtain ⟨s, rfl⟩ := (markedMemoryGhostOrigin m del l j).symm.surjective i
  cases s with
  | inl old =>
    simp only [markedMemoryGhostBirthIndexPerm, Equiv.trans_apply,
      Equiv.apply_symm_apply, Equiv.sumCongr_apply, Equiv.refl_apply,
      Sum.map_inl, markedMemoryGhostOrigin_old]
  | inr born =>
    simp only [markedMemoryGhostBirthIndexPerm, Equiv.trans_apply,
      Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inr,
      markedMemoryGhostOrigin_birth, markedMemoryGhostBirthPermute]

/-- The actual birth product measure is invariant, without any numeric-prime distinctness. -/
theorem markedMemoryGhostBirthMass_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) {B : ℕ}
    {m : MarkedRawMemory P B} {del : MarkedRawGhostDeletion m}
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l)
    (π : (j : J) → Equiv.Perm (Fin (l.1 j : ℕ))) :
    markedRawGhostBirthMass ν l (markedMemoryGhostBirthPermute l births π) =
      markedRawGhostBirthMass ν l births := by
  unfold markedRawGhostBirthMass markedMemoryGhostBirthPermute
  apply Finset.prod_congr rfl
  intro j _
  exact congrArg (fun r : ℝ => r / (Nat.factorial (l.1 j : ℕ) : ℝ))
    (Equiv.prod_comp (π j) (fun i => ν j (births j i)))

/-- Every genuinely symmetric memory observable is invariant under birth-slot reorderings. -/
theorem markedMemoryGhostTarget_symmetric_birth_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (f : MarkedRawMemory P B → ℂ)
    (hf : MarkedRawMemorySymmetric f) (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l)
    (π : (j : J) → Equiv.Perm (Fin (l.1 j : ℕ))) :
    f (markedRawGhostTargetMemory m z hz del l (markedMemoryGhostBirthPermute l births π)) =
      f (markedRawGhostTargetMemory m z hz del l births) := by
  rw [markedMemoryGhostTargetMemory_birth_permute]
  exact hf _ _

/-- The actual signed ghost coefficient, factorial birth mass, and symmetric target observable
are jointly invariant under birth-index permutations. -/
theorem markedMemoryGhostChoice_term_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ : ℝ) {B : ℕ} (f : MarkedRawMemory P B → ℂ)
    (hf : MarkedRawMemorySymmetric f) (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l)
    (π : (j : J) → Equiv.Perm (Fin (l.1 j : ℕ))) :
    ((markedRawGhostSignedCoefficient V qStage ρ m z hz del l *
      markedRawGhostBirthMass ν l (markedMemoryGhostBirthPermute l births π) : ℝ) : ℂ) *
        f (markedRawGhostTargetMemory m z hz del l (markedMemoryGhostBirthPermute l births π)) =
    ((markedRawGhostSignedCoefficient V qStage ρ m z hz del l *
      markedRawGhostBirthMass ν l births : ℝ) : ℂ) *
        f (markedRawGhostTargetMemory m z hz del l births) := by
  rw [markedMemoryGhostBirthMass_permute,
    markedMemoryGhostTarget_symmetric_birth_permute f hf]

end
end ArtinMatthews
