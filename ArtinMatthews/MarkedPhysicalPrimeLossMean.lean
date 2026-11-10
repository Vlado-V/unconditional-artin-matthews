module

public import ArtinMatthews.MarkedMinorArcRawState
public import Mathlib.CategoryTheory.Category.Basic
public import ArtinMatthews.MarkedMemoryTiltPrimewiseActual
public import ArtinMatthews.MarkedPhysicalJointPrimeLoss
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual one-prime loss has mean at most the sum of visit losses
divided by p+1. Correlations between visits remain exact; only the proved
uniform finite projective line is averaged. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedFiniteLineLoss {ι Λ : Type*} [DecidableEq Λ]
    (I : Finset ι) (r : ι → ℝ) (line : ι → Λ) (ell : Λ) : ℝ :=
  1-(∏ v ∈ I,if line v=ell then r v else 1)

theorem markedFiniteLineLoss_mem_unitInterval {ι Λ : Type*} [DecidableEq Λ]
    (I : Finset ι) (r : ι → ℝ) (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1) (line : ι → Λ) (ell : Λ) :
    0 ≤ markedFiniteLineLoss I r line ell ∧ markedFiniteLineLoss I r line ell ≤ 1 := by
  have hf (v : ι) (hv : v ∈ I) : 0 ≤ (if line v=ell then r v else 1) ∧ (if line v=ell then r v else 1) ≤ 1 := by
    split_ifs
    · exact hr v hv
    · exact ⟨zero_le_one,le_rfl⟩
  have hp0 := Finset.prod_nonneg (fun v hv => (hf v hv).1)
  have hp1 := Finset.prod_le_one₀ (fun v hv => (hf v hv).1) (fun v hv => (hf v hv).2)
  exact ⟨sub_nonneg.mpr hp1,by unfold markedFiniteLineLoss; linarith⟩

theorem markedFiniteLineLoss_le_hits {ι Λ : Type*} [DecidableEq Λ]
    (I : Finset ι) (r : ι → ℝ) (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1) (line : ι → Λ) (ell : Λ) :
    markedFiniteLineLoss I r line ell ≤ ∑ v ∈ I,(1-r v)*(if line v=ell then (1:ℝ) else 0) := by
  have hf (v : ι) (hv : v ∈ I) : 0 ≤ (if line v=ell then r v else 1) ∧ (if line v=ell then r v else 1) ≤ 1 := by
    split_ifs
    · exact hr v hv
    · exact ⟨zero_le_one,le_rfl⟩
  apply (marked_one_sub_prod_le_sum I _ hf).trans_eq
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> ring

theorem markedFiniteLineLoss_mean_le {ι Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (I : Finset ι) (r : ι → ℝ) (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1) (line : ι → Λ) :
    (∑ ell : Λ,markedFiniteLineLoss I r line ell)/(Fintype.card Λ:ℝ) ≤
      (∑ v ∈ I,(1-r v))/(Fintype.card Λ:ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ ell : Λ,∑ v ∈ I,(1-r v)*(if line v=ell then (1:ℝ) else 0) :=
      Finset.sum_le_sum (fun ell _ => markedFiniteLineLoss_le_hits I r hr line ell)
    _ = ∑ v ∈ I,∑ ell : Λ,(1-r v)*(if line v=ell then (1:ℝ) else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

def markedPhysicalPrimeLineLoss {ι : Type*} (p : Nat.Primes) (I : Finset ι) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (ell : MarkedRawPrimeLine p) : ℝ :=
  markedFiniteLineLoss I r (fun v => markedPrimePositionLine (p:ℕ) (z v) (hz v)) ell

theorem markedPhysicalPrimeLineLoss_mean_le {ι : Type*} (p : Nat.Primes) (I : Finset ι) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1) (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) :
    (∑ ell : MarkedRawPrimeLine p,markedPhysicalPrimeLineLoss p I r z hz ell)/((p:ℝ)+1) ≤
      (∑ v ∈ I,(1-r v))/((p:ℝ)+1) := by
  simpa only [markedPhysicalPrimeLineLoss,markedMemoryPrimeLine_card,Nat.cast_add,Nat.cast_one] using
    markedFiniteLineLoss_mean_le I r hr (fun v => markedPrimePositionLine (p:ℕ) (z v) (hz v))

end ArtinMatthews
