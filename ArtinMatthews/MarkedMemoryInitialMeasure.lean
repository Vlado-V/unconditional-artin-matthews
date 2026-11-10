module

public import ArtinMatthews.MarkedMemoryIndependentBirthWeight
public import ArtinMatthews.MarkedMemoryQueueState
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Initial active atoms belong to the source measure, not the
chronological birth weight. Their literal indexed product is recovered
from the actual first-time-zero identity fiber. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

def markedMemoryInitialIdentityEquiv (hempty : ∀ j,(d.lifespan j).initial=[]) :
    (Σ _ : J,Fin (pads+1)) ≃ {a : Σ j,A j // (d.lifespan a.1).first a.2=0} :=
  Equiv.ofBijective
    (fun b => ⟨⟨b.1,d.activeId 0 b.1 b.2⟩,by
      change (d.lifespan b.1).first (d.activeId 0 b.1 b.2)=0
      have h := (d.active_alive 0 (Nat.zero_le n) b.1 b.2).1
      omega⟩)
    ⟨by
      intro a b h
      have hh := congrArg Subtype.val h
      exact (Function.Embedding.sigmaMap (Function.Embedding.refl J)
        (fun j => d.activeId 0 j)).injective hh,
     by
      rintro ⟨⟨j,a⟩,ha⟩
      have hactive : (d.lifespan j).active 0 a := by
        by_contra hn
        have hm := ((d.lifespan j).initial_mem a).mpr ⟨ha.le,Nat.zero_le _,hn⟩
        rw [hempty j] at hm
        exact List.not_mem_nil hm
      obtain ⟨k,hk⟩ := (d.active_mem 0 (Nat.zero_le n) j a).mp hactive
      exact ⟨⟨j,k⟩,Subtype.ext (congrArg (Sigma.mk j) hk)⟩⟩

omit [∀ j,DecidableEq (A j)] in
theorem markedMemory_initial_identity_product (hempty : ∀ j,(d.lifespan j).initial=[])
    {R : Type*} [CommMonoid R] (f : (Σ j,A j) → R) :
    (∏ a : Σ j,A j,if (d.lifespan a.1).first a.2=0 then f a else 1)=
      ∏ j,∏ k : Fin (pads+1),f ⟨j,d.activeId 0 j k⟩ := by
  rw [← Finset.prod_filter (fun a : Σ j,A j => (d.lifespan a.1).first a.2=0) f]
  rw [Finset.prod_subtype (p := fun a : Σ j,A j => (d.lifespan a.1).first a.2=0)
    (Finset.univ.filter (fun a : Σ j,A j => (d.lifespan a.1).first a.2=0))
    (by simp) f]
  rw [← Equiv.prod_comp (markedMemoryInitialIdentityEquiv hZ d hempty)]
  rw [Fintype.prod_sigma]
  rfl

def markedMemoryInitialIdentityMass (ν : (j : J) → ↥(P j) → ℝ) : ℝ :=
  ∏ a : Σ j,A j,if (d.lifespan a.1).first a.2=0 then ν a.1 (d.particle a.1 a.2).1 else 1

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryInitialIdentityMass_eq (hempty : ∀ j,(d.lifespan j).initial=[])
    (ν : (j : J) → ↥(P j) → ℝ) :
    markedMemoryInitialIdentityMass hZ d ν=
      markedRawActiveMass ν (fun j k => (d.particle j (d.activeId 0 j k)).1) :=
  markedMemory_initial_identity_product hZ d hempty (fun a => ν a.1 (d.particle a.1 a.2).1)

theorem markedMemory_initial_memory_empty (hempty : ∀ j,(d.lifespan j).initial=[]) :
    markedMemoryIndependentMemory hZ d 0 (by omega)=markedRawBoundaryEmptyMemory P B := by
  apply markedMemoryState_eq_of_lists
  intro j
  rw [markedMemoryIndependentMemory,markedMemoryLabeledQueueState_list]
  simp [markedMemoryIndependentQueue,markedMemoryPendingQueueAt,hempty,
    markedRawBoundaryEmptyMemory]

theorem markedMemoryInitialIdentityMass_source (hempty : ∀ j,(d.lifespan j).initial=[])
    (ν : (j : J) → ↥(P j) → ℝ) :
    markedRawStateMass ν (markedMemoryIndependentState hZ d 0 (Nat.zero_le n))=
      markedMemoryInitialIdentityMass hZ d ν := by
  rw [markedRawStateMass]
  change markedRawActiveMass ν (fun j k => (d.particle j (d.activeId 0 j k)).1)*
    markedRawMemoryMass ν (markedMemoryIndependentMemory hZ d 0 (by omega))=_
  rw [markedMemory_initial_memory_empty hZ d hempty,markedRawBoundaryEmptyMemory_mass,mul_one]
  exact (markedMemoryInitialIdentityMass_eq hZ d hempty ν).symm

def markedMemoryCompletedBirthMass (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (a : Σ j,A j) : ℝ :=
  (if (d.lifespan a.1).first a.2 % 2=1 then V a.1 else 1)*ν a.1 (d.particle a.1 a.2).1

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryCompletedBirthMass_eq (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (a : Σ j,A j) :
    markedMemoryCompletedBirthMass hZ d ν V a=
      (if (d.lifespan a.1).first a.2=0 then ν a.1 (d.particle a.1 a.2).1 else 1)*
        markedMemoryIndependentBirthMass hZ d ν V a := by
  unfold markedMemoryCompletedBirthMass markedMemoryIndependentBirthMass
  split_ifs <;> simp_all

theorem markedMemory_source_birth_product (hempty : ∀ j,(d.lifespan j).initial=[])
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (g : (Σ j,A j) → ℝ) :
    markedRawStateMass ν (markedMemoryIndependentState hZ d 0 (Nat.zero_le n))*
        (∏ a : Σ j,A j,markedMemoryIndependentBirthMass hZ d ν V a*g a)=
      ∏ a : Σ j,A j,markedMemoryCompletedBirthMass hZ d ν V a*g a := by
  rw [markedMemoryInitialIdentityMass_source hZ d hempty,markedMemoryInitialIdentityMass,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  rw [markedMemoryCompletedBirthMass_eq]
  ring

end
end ArtinMatthews
