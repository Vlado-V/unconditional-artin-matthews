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

/-! The literal prime support of a fixed ordered physical label path
has a budget derived from its slots, including repeated labels/visits. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalLabelSet_card_le {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (a : MarkedPhysicalMarking P M) (j : J) : (markedPhysicalLabelSet a j).card≤M := by
  exact (Finset.card_image_le).trans_eq (Fintype.card_fin M)

theorem markedPhysicalActivePrimes_card_le {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (a : MarkedPhysicalMarking P M) :
    (markedPhysicalActivePrimes a).card≤Fintype.card J*M := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _j : J,M := Finset.sum_le_sum (fun j _ => markedPhysicalLabelSet_card_le a j)
    _ = _ := by simp

theorem markedPhysicalPathUsedPrimes_card_le {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) :
    (markedPhysicalPathUsedPrimes I a).card≤I.card*(Fintype.card J*M) := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _v ∈ I,Fintype.card J*M :=
      Finset.sum_le_sum (fun v _ => markedPhysicalActivePrimes_card_le (a v))
    _ = _ := by simp

theorem markedPhysicalPathUsedPrimes_prod_le_exp {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (L : ℝ) (hL : 0≤L) (hP : ∀ j p,p∈P j → (p:ℝ)≤Real.exp L) :
    (∏ p ∈ markedPhysicalPathUsedPrimes I a,(p:ℝ))≤
      Real.exp ((I.card:ℝ)*(Fintype.card J:ℝ)*(M:ℝ)*L) := by
  have hp (p : ℕ) (hm : p∈markedPhysicalPathUsedPrimes I a) : (p:ℝ)≤Real.exp L := by
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp (markedPhysicalPathUsedPrimes_subset I a hm)
    exact hP j p hj
  calc
    _ ≤ ∏ _p ∈ markedPhysicalPathUsedPrimes I a,Real.exp L :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) hp
    _ = Real.exp (((markedPhysicalPathUsedPrimes I a).card:ℝ)*L) := by
      rw [Finset.prod_const,← Real.exp_nat_mul]
    _ ≤ Real.exp ((I.card:ℝ)*(Fintype.card J:ℝ)*(M:ℝ)*L) := by
      apply Real.exp_le_exp.mpr
      have hc : ((markedPhysicalPathUsedPrimes I a).card:ℝ)≤
          (I.card:ℝ)*(Fintype.card J:ℝ)*(M:ℝ) := by
        have hh : ((markedPhysicalPathUsedPrimes I a).card:ℝ)≤
            ((I.card*(Fintype.card J*M):ℕ):ℝ) :=
          Nat.cast_le.mpr (markedPhysicalPathUsedPrimes_card_le I a)
        simpa only [Nat.cast_mul,mul_assoc] using hh
      exact mul_le_mul_of_nonneg_right hc hL

end
end ArtinMatthews
