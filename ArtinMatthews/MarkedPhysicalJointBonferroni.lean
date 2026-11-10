module

public import ArtinMatthews.MarkedPhysicalJointPrimeDamping
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

/-! Performed pointwise Bonferroni truncation of the original joint
physical damping. Used-prime factors stay exact. Every monomial retains
its literal inactive prime set; no residue expectation is assumed. -/

noncomputable section
namespace ArtinMatthews
open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}

def markedPhysicalUsedPrimeWeight (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (r : ι → ℝ) (u : ι → ℕ) : ℝ :=
  ∏ p ∈ markedPhysicalPathUsedPrimes I a,markedPhysicalPrimePathFactor I a r u p

def markedPhysicalJointBonferroni (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (r : ι → ℝ) (u : ι → ℕ) (k : ℕ) : ℝ :=
  markedPhysicalUsedPrimeWeight I a r u*
    BonferroniDensity.densityPolynomial k (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a)
      (markedPhysicalInactivePrimeLoss I a r u)

def markedPhysicalJointBonferroniTail (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (r : ι → ℝ) (u : ι → ℕ) (k : ℕ) : ℝ :=
  markedPhysicalUsedPrimeWeight I a r u*
    BonferroniDensity.elementarySum (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a)
      (markedPhysicalInactivePrimeLoss I a r u) k

def markedPhysicalJointBonferroniMonomial (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (r : ι → ℝ) (u : ι → ℕ) (T : Finset ℕ) : ℝ :=
  markedPhysicalUsedPrimeWeight I a r u*∏ p ∈ T,markedPhysicalInactivePrimeLoss I a r u p

theorem markedPhysicalUsedPrimeWeight_mem_unitInterval
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1) (u : ι → ℕ) :
    0 ≤ markedPhysicalUsedPrimeWeight I a r u ∧ markedPhysicalUsedPrimeWeight I a r u ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun p _ => (markedPhysicalPrimePathFactor_mem_unitInterval I a r hr u p).1)
  · exact Finset.prod_le_one₀ (fun p _ => (markedPhysicalPrimePathFactor_mem_unitInterval I a r hr u p).1)
      (fun p _ => (markedPhysicalPrimePathFactor_mem_unitInterval I a r hr u p).2)

theorem markedPhysicalJointBonferroni_bounds
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1) (u : ι → ℕ) (m : ℕ) :
    markedPhysicalJointBonferroni I a r u (2*m+1) ≤ markedPhysicalJointPrimeWeight I a r u ∧
      markedPhysicalJointPrimeWeight I a r u ≤ markedPhysicalJointBonferroni I a r u (2*m) := by
  have hb := BonferroniDensity.densityPolynomial_bounds
    (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a) (markedPhysicalInactivePrimeLoss I a r u)
    (fun p _ => (markedPhysicalInactivePrimeLoss_mem_unitInterval I a r hr u p).1)
    (fun p _ => (markedPhysicalInactivePrimeLoss_mem_unitInterval I a r hr u p).2) m
  rw [markedPhysicalJointPrimeWeight_split hdis]
  exact ⟨mul_le_mul_of_nonneg_left hb.1 (markedPhysicalUsedPrimeWeight_mem_unitInterval I a r hr u).1,
    mul_le_mul_of_nonneg_left hb.2 (markedPhysicalUsedPrimeWeight_mem_unitInterval I a r hr u).1⟩

theorem markedPhysicalJointBonferroni_gap
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ) (u : ι → ℕ) (m : ℕ) :
    markedPhysicalJointBonferroni I a r u (2*m)-markedPhysicalJointBonferroni I a r u (2*m+1) =
      markedPhysicalJointBonferroniTail I a r u (2*m+1) := by
  unfold markedPhysicalJointBonferroni markedPhysicalJointBonferroniTail
  rw [← mul_sub,BonferroniDensity.densityPolynomial_gap]

theorem markedPhysicalJointBonferroniTail_nonneg
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1) (u : ι → ℕ) (k : ℕ) :
    0 ≤ markedPhysicalJointBonferroniTail I a r u k := by
  exact mul_nonneg (markedPhysicalUsedPrimeWeight_mem_unitInterval I a r hr u).1
    (BonferroniDensity.elementarySum_nonneg _ _
      (fun p _ => (markedPhysicalInactivePrimeLoss_mem_unitInterval I a r hr u p).1) k)

theorem markedPhysicalJointBonferroni_upper_error
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1) (u : ι → ℕ) (m : ℕ) :
    |markedPhysicalJointPrimeWeight I a r u-markedPhysicalJointBonferroni I a r u (2*m)| ≤
      markedPhysicalJointBonferroniTail I a r u (2*m+1) := by
  have hb := markedPhysicalJointBonferroni_bounds hdis I a r hr u m
  have hg := markedPhysicalJointBonferroni_gap I a r u m
  rw [abs_of_nonpos (sub_nonpos.mpr hb.2)]
  linarith

theorem markedPhysicalJointBonferroni_complex_error
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1) (u : ι → ℕ) (m : ℕ) (κ : ℂ) :
    ‖κ*(markedPhysicalJointPrimeWeight I a r u:ℂ)-κ*(markedPhysicalJointBonferroni I a r u (2*m):ℂ)‖ ≤
      ‖κ‖*markedPhysicalJointBonferroniTail I a r u (2*m+1) := by
  rw [← mul_sub,← Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (markedPhysicalJointBonferroni_upper_error hdis I a r hr u m) (norm_nonneg _)

theorem markedPhysicalJointBonferroniMonomial_mem_unitInterval
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1) (u : ι → ℕ) (T : Finset ℕ) :
    0 ≤ markedPhysicalJointBonferroniMonomial I a r u T ∧ markedPhysicalJointBonferroniMonomial I a r u T ≤ 1 := by
  have hm := markedPhysicalUsedPrimeWeight_mem_unitInterval I a r hr u
  have hp0 : 0 ≤ ∏ p ∈ T,markedPhysicalInactivePrimeLoss I a r u p :=
    Finset.prod_nonneg (fun p _ => (markedPhysicalInactivePrimeLoss_mem_unitInterval I a r hr u p).1)
  have hp1 : (∏ p ∈ T,markedPhysicalInactivePrimeLoss I a r u p) ≤ 1 :=
    Finset.prod_le_one₀ (fun p _ => (markedPhysicalInactivePrimeLoss_mem_unitInterval I a r hr u p).1)
      (fun p _ => (markedPhysicalInactivePrimeLoss_mem_unitInterval I a r hr u p).2)
  exact ⟨mul_nonneg hm.1 hp0,(mul_le_mul hm.2 hp1 hp0 zero_le_one).trans_eq (one_mul _)⟩

theorem markedPhysicalJointBonferroni_monomials
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ) (u : ι → ℕ) (k : ℕ) :
    markedPhysicalJointBonferroni I a r u k =
      ∑ j ∈ Finset.range (k+1),(-1:ℝ)^j*
        ∑ T ∈ (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a).powersetCard j,
          markedPhysicalJointBonferroniMonomial I a r u T := by
  unfold markedPhysicalJointBonferroni BonferroniDensity.densityPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold BonferroniDensity.elementarySum markedPhysicalJointBonferroniMonomial
  rw [← Finset.mul_sum]
  ring

end ArtinMatthews
