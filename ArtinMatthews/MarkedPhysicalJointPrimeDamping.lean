module

public import ArtinMatthews.MarkedPhysicalPrimeHitProduct
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

/-! Exact joint-prime physical damping. All primes active somewhere on
the path retain their complete factors. Every other prime contributes the
literal number 1-X_p in [0,1], before any residue averaging. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}

def markedPhysicalJointPrimeWeight (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (r : ι → ℝ) (u : ι → ℕ) : ℝ :=
  ∏ v ∈ I,markedPhysicalInactivePrimeWeight P (a v) (r v) (u v)

def markedPhysicalPrimePathFactor (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (r : ι → ℝ) (u : ι → ℕ) (p : ℕ) : ℝ :=
  ∏ v ∈ I,markedPhysicalPrimeVisitFactor (markedPhysicalActivePrimes (a v)) (r v) (u v) p

def markedPhysicalPathUsedPrimes (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) : Finset ℕ :=
  I.biUnion (fun v => markedPhysicalActivePrimes (a v))

def markedPhysicalInactivePrimeLoss (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (r : ι → ℝ) (u : ι → ℕ) (p : ℕ) : ℝ :=
  1-markedPhysicalPrimePathFactor I a r u p

theorem markedPhysicalPathUsedPrimes_subset (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) :
    markedPhysicalPathUsedPrimes I a ⊆ markedPhysicalBandPrimes P := by
  intro p hp
  obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp hp
  exact markedPhysicalActivePrimes_subset (a v) hv

theorem markedPhysicalJointPrimeWeight_global
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ) (u : ι → ℕ) :
    markedPhysicalJointPrimeWeight I a r u =
      ∏ p ∈ markedPhysicalBandPrimes P,markedPhysicalPrimePathFactor I a r u p := by
  unfold markedPhysicalJointPrimeWeight
  simp_rw [markedPhysicalInactivePrimeWeight_global P hdis]
  rw [Finset.prod_comm]
  rfl

theorem markedPhysicalPrimePathFactor_mem_unitInterval
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1) (u : ι → ℕ) (p : ℕ) :
    0 ≤ markedPhysicalPrimePathFactor I a r u p ∧ markedPhysicalPrimePathFactor I a r u p ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun v hv => (markedPhysicalPrimeVisitFactor_mem_unitInterval _ (hr v hv).1 (hr v hv).2 _ _).1)
  · exact Finset.prod_le_one₀ (fun v hv => (markedPhysicalPrimeVisitFactor_mem_unitInterval _ (hr v hv).1 (hr v hv).2 _ _).1)
      (fun v hv => (markedPhysicalPrimeVisitFactor_mem_unitInterval _ (hr v hv).1 (hr v hv).2 _ _).2)

theorem markedPhysicalInactivePrimeLoss_mem_unitInterval
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1) (u : ι → ℕ) (p : ℕ) :
    0 ≤ markedPhysicalInactivePrimeLoss I a r u p ∧ markedPhysicalInactivePrimeLoss I a r u p ≤ 1 := by
  have h := markedPhysicalPrimePathFactor_mem_unitInterval I a r hr u p
  exact ⟨sub_nonneg.mpr h.2,by unfold markedPhysicalInactivePrimeLoss; linarith⟩

theorem markedPhysicalInactivePrimeLoss_eq (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (r : ι → ℝ) (u : ι → ℕ) {p : ℕ} (hp : p ∉ markedPhysicalPathUsedPrimes I a) :
    markedPhysicalInactivePrimeLoss I a r u p =
      1-(∏ v ∈ I,(1-(1-r v)*(if p ∣ u v then (1:ℝ) else 0))) := by
  unfold markedPhysicalInactivePrimeLoss markedPhysicalPrimePathFactor
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  have hn : p ∉ markedPhysicalActivePrimes (a v) := fun hm => hp (Finset.mem_biUnion.mpr ⟨v,hv,hm⟩)
  unfold markedPhysicalPrimeVisitFactor
  rw [ite_eq_right hn]
  split_ifs <;> ring

theorem markedPhysicalJointPrimeWeight_split
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ) (u : ι → ℕ) :
    markedPhysicalJointPrimeWeight I a r u =
      (∏ p ∈ markedPhysicalPathUsedPrimes I a,markedPhysicalPrimePathFactor I a r u p)*
        ∏ p ∈ markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a,
          (1-markedPhysicalInactivePrimeLoss I a r u p) := by
  rw [markedPhysicalJointPrimeWeight_global hdis]
  calc
    _ = (∏ p ∈ markedPhysicalPathUsedPrimes I a,markedPhysicalPrimePathFactor I a r u p)*
        ∏ p ∈ markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a,markedPhysicalPrimePathFactor I a r u p := by
      rw [mul_comm]
      exact (Finset.prod_sdiff (markedPhysicalPathUsedPrimes_subset I a)).symm
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro p _
      unfold markedPhysicalInactivePrimeLoss
      ring

end ArtinMatthews
