module

public import ArtinMatthews.MarkedMemoryHistoryBirthTarget
public import ArtinMatthews.MarkedMemoryHistoryBirthPermutations
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Tactic.ENatToNat
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

/-! Exact unordered birth sums for the actual signed ghost operation.
The restriction is explicit: each birth tuple is injective and avoids the
specified old primes. No quotient of a tuple with repeated values is used. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryBirthFamilySet {J : Type*} {X : J → Type*} {n : J → ℕ}
    (e : (j : J) → Fin (n j) ↪ X j) : (j : J) → MarkedMemoryBirthSets (X j) (n j) :=
  fun j => markedMemoryBirthSet (e j)

def markedMemoryBirthFamilyFiberEquiv {J : Type*} {X : J → Type*} {n : J → ℕ}
    (S : (j : J) → MarkedMemoryBirthSets (X j) (n j)) :
    {e : (j : J) → Fin (n j) ↪ X j // markedMemoryBirthFamilySet e = S} ≃
      ((j : J) → {e : Fin (n j) ↪ X j // markedMemoryBirthSet e = S j}) where
  toFun e j := ⟨e.1 j, congrFun e.2 j⟩
  invFun e := ⟨fun j => (e j).1, funext (fun j => (e j).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem markedMemoryBirthFamilyFiber_card {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {n : J → ℕ}
    (S : (j : J) → MarkedMemoryBirthSets (X j) (n j)) :
    Fintype.card {e : (j : J) → Fin (n j) ↪ X j // markedMemoryBirthFamilySet e = S} =
      ∏ j, (n j).factorial := by
  classical
  rw [Fintype.card_congr (markedMemoryBirthFamilyFiberEquiv S), Fintype.card_pi]
  exact Finset.prod_congr rfl (fun j _ => markedMemoryBirthFiber_card (S j))

theorem markedMemoryBirthFamily_normalized_sum {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {n : J → ℕ}
    (F : ((j : J) → MarkedMemoryBirthSets (X j) (n j)) → ℂ) :
    (∑ e : (j : J) → Fin (n j) ↪ X j,
      F (markedMemoryBirthFamilySet e) / (∏ j, ((n j).factorial : ℂ))) = ∑ S, F S := by
  classical
  rw [← Fintype.sum_fiberwise (markedMemoryBirthFamilySet (X := X) (n := n))]
  apply Finset.sum_congr rfl
  intro S _
  have hn : (∏ j, ((n j).factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  simp only [show ∀ e : {e : (j : J) → Fin (n j) ↪ X j // markedMemoryBirthFamilySet e = S},
    F (markedMemoryBirthFamilySet e.1) / (∏ j, ((n j).factorial : ℂ)) =
      F S / (∏ j, ((n j).factorial : ℂ)) from fun e => by rw [e.2]]
  rw [Finset.sum_const, Finset.card_univ, markedMemoryBirthFamilyFiber_card, nsmul_eq_mul]
  push_cast
  field_simp

def markedMemoryBirthFamilyCanonical {J : Type*} {X : J → Type*} {n : J → ℕ}
    (S : (j : J) → MarkedMemoryBirthSets (X j) (n j)) : (j : J) → Fin (n j) ↪ X j :=
  fun j => markedMemoryBirthCanonical (S j)

theorem markedMemoryBirthFamily_normalized_symmetric_sum {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {n : J → ℕ}
    (W : ((j : J) → Fin (n j) ↪ X j) → ℂ)
    (hW : ∀ e (π : (j : J) → Equiv.Perm (Fin (n j))),
      W (fun j => markedMemoryBirthReindex (e j) (π j)) = W e) :
    (∑ e : (j : J) → Fin (n j) ↪ X j, W e / (∏ j, ((n j).factorial : ℂ))) =
      ∑ S : (j : J) → MarkedMemoryBirthSets (X j) (n j), W (markedMemoryBirthFamilyCanonical S) := by
  classical
  have heq (e : (j : J) → Fin (n j) ↪ X j) :
      W e = W (markedMemoryBirthFamilyCanonical (markedMemoryBirthFamilySet e)) := by
    have hb (j : J) :
        markedMemoryBirthBatch (markedMemoryBirthCanonical (markedMemoryBirthSet (e j))) =
          markedMemoryBirthBatch (e j) :=
      congrArg Subtype.val (markedMemoryBirthCanonical_set (markedMemoryBirthSet (e j)))
    choose π hπ _ using fun j => (markedMemoryBirth_eq_iff_reindex _ _).mp (hb j)
    have hp : (fun j => markedMemoryBirthReindex
        (markedMemoryBirthCanonical (markedMemoryBirthSet (e j))) (π j)) = e := funext hπ
    exact (congrArg W hp).symm.trans (hW _ π)
  calc
    _ = ∑ e : (j : J) → Fin (n j) ↪ X j,
        W (markedMemoryBirthFamilyCanonical (markedMemoryBirthFamilySet e)) /
          (∏ j, ((n j).factorial : ℂ)) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [heq e]
    _ = _ := markedMemoryBirthFamily_normalized_sum (n := n)
      (fun S => W (markedMemoryBirthFamilyCanonical S))

/-- Forbidden-prime avoidance and pairwise distinctness are restrictions
on actual numeric birth labels, separately in each original band. -/
def MarkedMemoryGhostBirthsAvoid {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
    {del : MarkedRawGhostDeletion m} (l : MarkedRawGhostBirthSizes m del)
    (forbidden : Finset Nat.Primes) (births : MarkedRawGhostBirthLabels l) : Prop :=
  (∀ j, Function.Injective (births j)) ∧ ∀ j k, (births j k).1 ∉ forbidden

abbrev MarkedMemoryAllowedBirthPrime {J : Type*} {P : J → Finset Nat.Primes}
    (forbidden : Finset Nat.Primes) (j : J) := {p : ↥(P j) // p.1 ∉ forbidden}

def markedMemoryGhostBirthsOfEmbedding {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
    {del : MarkedRawGhostDeletion m} (l : MarkedRawGhostBirthSizes m del)
    (forbidden : Finset Nat.Primes)
    (e : (j : J) → Fin (l.1 j : ℕ) ↪ MarkedMemoryAllowedBirthPrime (P := P) forbidden j) :
    MarkedRawGhostBirthLabels l := fun j k => (e j k).1

def markedMemoryGhostBirthsAvoidEquiv {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
    {del : MarkedRawGhostDeletion m} (l : MarkedRawGhostBirthSizes m del)
    (forbidden : Finset Nat.Primes) :
    {births : MarkedRawGhostBirthLabels l // MarkedMemoryGhostBirthsAvoid l forbidden births} ≃
      ((j : J) → Fin (l.1 j : ℕ) ↪ MarkedMemoryAllowedBirthPrime (P := P) forbidden j) where
  toFun b j :=
    { toFun := fun k => ⟨b.1 j k, b.2.2 j k⟩
      inj' := fun _ _ h => b.2.1 j (congrArg Subtype.val h) }
  invFun e := ⟨markedMemoryGhostBirthsOfEmbedding l forbidden e,
    ⟨fun j _ _ h => (e j).injective (Subtype.ext h), fun j k => (e j k).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The numerator of the original ordered birth mass, without its actual
factorial denominator. -/
def markedMemoryGhostBirthProduct {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {B : ℕ} {m : MarkedRawMemory P B} {del : MarkedRawGhostDeletion m}
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) : ℝ :=
  ∏ j, ∏ k, ν j (births j k)

theorem markedMemoryGhostBirthMass_product {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {B : ℕ} {m : MarkedRawMemory P B} {del : MarkedRawGhostDeletion m}
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) :
    markedRawGhostBirthMass ν l births =
      markedMemoryGhostBirthProduct ν l births / (∏ j, ((l.1 j : ℕ).factorial : ℝ)) := by
  simp only [markedRawGhostBirthMass, markedMemoryGhostBirthProduct, Finset.prod_div_distrib]

theorem markedMemoryGhostBirthProduct_permute {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {B : ℕ} {m : MarkedRawMemory P B} {del : MarkedRawGhostDeletion m}
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l)
    (π : (j : J) → Equiv.Perm (Fin (l.1 j : ℕ))) :
    markedMemoryGhostBirthProduct ν l (markedMemoryGhostBirthPermute l births π) =
      markedMemoryGhostBirthProduct ν l births := by
  unfold markedMemoryGhostBirthProduct markedMemoryGhostBirthPermute
  exact Finset.prod_congr rfl (fun j _ => Equiv.prod_comp (π j) (fun k => ν j (births j k)))

/-- Exact signed ghost birth quotient at fixed actual old deletion and
birth sizes. Each l_j! cancels its enumeration fiber, all forbidden-prime
restrictions and the symmetric target observable remain literal. -/
theorem markedMemoryGhostBirths_unordered_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ : ℝ) {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (forbidden : Finset Nat.Primes)
    (f : MarkedRawMemory P B → ℂ) (hf : MarkedRawMemorySymmetric f) :
    (∑ births : MarkedRawGhostBirthLabels l,
      if MarkedMemoryGhostBirthsAvoid l forbidden births then
        ((markedRawGhostSignedCoefficient V qStage ρ m z hz del l *
          markedRawGhostBirthMass ν l births : ℝ) : ℂ) *
            f (markedRawGhostTargetMemory m z hz del l births)
      else 0) =
    ∑ S : (j : J) → MarkedMemoryBirthSets
        (MarkedMemoryAllowedBirthPrime (P := P) forbidden j) (l.1 j : ℕ),
      ((markedRawGhostSignedCoefficient V qStage ρ m z hz del l *
        (∏ j, ∏ p ∈ (S j).1, ν j p.1) : ℝ) : ℂ) *
          f (markedRawGhostTargetMemory m z hz del l
            (markedMemoryGhostBirthsOfEmbedding l forbidden (markedMemoryBirthFamilyCanonical S))) := by
  classical
  let C := markedRawGhostSignedCoefficient V qStage ρ m z hz del l
  let E := (j : J) → Fin (l.1 j : ℕ) ↪ MarkedMemoryAllowedBirthPrime (P := P) forbidden j
  let W (e : E) : ℂ :=
    ((C * markedMemoryGhostBirthProduct ν l (markedMemoryGhostBirthsOfEmbedding l forbidden e) : ℝ) : ℂ) *
      f (markedRawGhostTargetMemory m z hz del l (markedMemoryGhostBirthsOfEmbedding l forbidden e))
  have hW (e : E) (π : (j : J) → Equiv.Perm (Fin (l.1 j : ℕ))) :
      W (fun j => markedMemoryBirthReindex (e j) (π j)) = W e := by
    change ((C * markedMemoryGhostBirthProduct ν l
      (markedMemoryGhostBirthPermute l (markedMemoryGhostBirthsOfEmbedding l forbidden e) π) : ℝ) : ℂ) *
        f (markedRawGhostTargetMemory m z hz del l
          (markedMemoryGhostBirthPermute l (markedMemoryGhostBirthsOfEmbedding l forbidden e) π)) = W e
    rw [markedMemoryGhostBirthProduct_permute,
      markedMemoryGhostTarget_symmetric_birth_permute f hf]
  have hterm (e : E) :
      ((C * markedRawGhostBirthMass ν l (markedMemoryGhostBirthsOfEmbedding l forbidden e) : ℝ) : ℂ) *
        f (markedRawGhostTargetMemory m z hz del l (markedMemoryGhostBirthsOfEmbedding l forbidden e)) =
      W e / (∏ j, ((l.1 j : ℕ).factorial : ℂ)) := by
    rw [markedMemoryGhostBirthMass_product]
    dsimp only [W]
    push_cast
    ring
  calc
    _ = ∑ births : {births : MarkedRawGhostBirthLabels l // MarkedMemoryGhostBirthsAvoid l forbidden births},
        ((C * markedRawGhostBirthMass ν l births.1 : ℝ) : ℂ) *
          f (markedRawGhostTargetMemory m z hz del l births.1) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ e : E, W e / (∏ j, ((l.1 j : ℕ).factorial : ℂ)) := by
      rw [← Equiv.sum_comp (markedMemoryGhostBirthsAvoidEquiv l forbidden).symm]
      exact Finset.sum_congr rfl (fun e _ => hterm e)
    _ = ∑ S, W (markedMemoryBirthFamilyCanonical S) :=
      markedMemoryBirthFamily_normalized_symmetric_sum W hW
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      dsimp only [W, markedMemoryGhostBirthProduct, markedMemoryGhostBirthsOfEmbedding,
        markedMemoryBirthFamilyCanonical]
      congr 2
      change C * _ = C * _
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      have hp := markedMemoryBirth_product (fun p : MarkedMemoryAllowedBirthPrime (P := P) forbidden j => p.1)
        (fun p : ↥(P j) => (ν j p : ℂ)) (markedMemoryBirthCanonical (S j))
      rw [show markedMemoryBirthBatch (markedMemoryBirthCanonical (S j)) = (S j).1 from
        congrArg Subtype.val (markedMemoryBirthCanonical_set (S j))] at hp
      exact_mod_cast hp

end
end ArtinMatthews
