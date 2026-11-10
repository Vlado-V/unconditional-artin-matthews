module

public import ArtinMatthews.MarkedBonferroniTail
public import ArtinMatthews.MarkedPhysicalBonferroniResidue
public import ArtinMatthews.MarkedPhysicalBonferroniMonomialMean
public import ArtinMatthews.MarkedPhysicalResidueMonomialBounds
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

/-! Sum of the actual selected-modulus residue means in the odd tail.
Each monomial uses its own performed modulus. The independent one-prime
bound yields the genuine elementary-sum/factorial estimate. -/

noncomputable section
namespace ArtinMatthews
open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}

def markedPhysicalSelectedMonomialMean (hP : ∀ j p,p∈P j → p.Prime)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ) : ℝ :=
  if hT : T ⊆ markedPhysicalBandPrimes P then
    let S := markedPhysicalBonferroniModulus I a T
    let _ : NeZero S := ⟨(markedPhysicalBonferroniModulus_pos hP I a hT).ne'⟩
    (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
      markedPhysicalResidueBonferroniMonomial (markedPhysicalBonferroniModulus_squarefree hP I a hT) g I a r z hz T)/
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ)
  else 0

def markedPhysicalBonferroniTailMean (hP : ∀ j p,p∈P j → p.Prime)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ) : ℝ :=
  ∑ T ∈ (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a).powersetCard k,
    markedPhysicalSelectedMonomialMean hP I a r z hz T

theorem markedPhysicalSelectedMonomialMean_nonneg (hP : ∀ j p,p∈P j → p.Prime)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ) :
    0 ≤ markedPhysicalSelectedMonomialMean hP I a r z hz T := by
  unfold markedPhysicalSelectedMonomialMean
  split_ifs
  · exact div_nonneg (Finset.sum_nonneg (fun g _ =>
      (markedPhysicalResidueBonferroniMonomial_mem_unitInterval _ g I a r hr z hz T).1)) (Nat.cast_nonneg _)
  · exact le_rfl

theorem markedPhysicalBonferroniTailMean_nonneg (hP : ∀ j p,p∈P j → p.Prime)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ) :
    0 ≤ markedPhysicalBonferroniTailMean hP I a r z hz k :=
  Finset.sum_nonneg (fun T _ => markedPhysicalSelectedMonomialMean_nonneg hP I a r hr z hz T)

theorem markedPhysicalSelectedMonomialMean_le (hP : ∀ j p,p∈P j → p.Prime)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ)
    (hT : T ⊆ markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a) :
    markedPhysicalSelectedMonomialMean hP I a r z hz T ≤ ∏ p ∈ T,(∑ v ∈ I,(1-r v))/((p:ℝ)+1) := by
  have hTP : T ⊆ markedPhysicalBandPrimes P := fun p hp => (Finset.mem_sdiff.mp (hT hp)).1
  let S := markedPhysicalBonferroniModulus I a T
  let : NeZero S := ⟨(markedPhysicalBonferroniModulus_pos hP I a hTP).ne'⟩
  simp only [markedPhysicalSelectedMonomialMean,dite_eq_left hTP]
  exact markedPhysicalResidueBonferroniMonomial_mean_le _ I a r hr z hz T
    (fun p hp => markedPhysicalBonferroniModulus_mem_primeFactors hP I a hTP (Finset.mem_union_right _ hp))
    (fun p hp => (Finset.mem_sdiff.mp (hT hp)).2)

theorem markedPhysicalBonferroniTailMean_le_elementary (hP : ∀ j p,p∈P j → p.Prime)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ) :
    markedPhysicalBonferroniTailMean hP I a r z hz k ≤
      BonferroniDensity.elementarySum (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a)
        (fun p => (∑ v ∈ I,(1-r v))/((p:ℝ)+1)) k := by
  apply Finset.sum_le_sum
  intro T hT
  exact markedPhysicalSelectedMonomialMean_le hP I a r hr z hz T (Finset.mem_powersetCard.mp hT).1

theorem markedPhysicalBonferroniTailMean_le_factorial (hP : ∀ j p,p∈P j → p.Prime)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ) :
    markedPhysicalBonferroniTailMean hP I a r z hz k ≤
      markedFactorialTail ((∑ v ∈ I,(1-r v))*
        ∑ p ∈ markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a,1/((p:ℝ)+1)) k := by
  have hη : 0 ≤ ∑ v ∈ I,(1-r v) := Finset.sum_nonneg (fun v hv => sub_nonneg.mpr (hr v hv).2)
  have hs : (∑ p ∈ markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a,
      (∑ v ∈ I,(1-r v))/((p:ℝ)+1)) =
      (∑ v ∈ I,(1-r v))*(∑ p ∈ markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a,1/((p:ℝ)+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  apply (markedPhysicalBonferroniTailMean_le_elementary hP I a r hr z hz k).trans
  exact BonferroniDensity.elementarySum_le_pow_div_factorial _ _
    (fun _ _ => div_nonneg hη (by positivity)) (by positivity) (le_of_eq hs) k

end ArtinMatthews
