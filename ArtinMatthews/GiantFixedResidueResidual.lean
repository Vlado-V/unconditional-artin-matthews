module

public import ArtinMatthews.GiantFixedResiduePolynomial
public import ArtinMatthews.MarkedProgressionResidual
public import ArtinMatthews.MarkedProgressionComparison
public import ArtinMatthews.MarkedProgressionCoprime
public import ArtinMatthews.MarkedProgressionPositive
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual selected residual in a fixed unit progression. The full
positive omitted layer controls the restricted layer by inclusion. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem giantFixedResidue_weighted_residual_summed_error (M a : ℕ)
    (hM : 0<M) (ha : a.Coprime M) (P S : Finset ℕ)
    (hcop : ∀ p∈P,p.Coprime M)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (m R : ℕ)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0) (hf0 : ∀ t, 0 ≤ f t) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ giantFixedResidueSet M a r T,
          f u * markedWeightedResidual P S θ u) -
        giantFixedResidueScale M r (∫ t in Set.Ioc 0 T, f t) * markedWeightedModel P S θ|) ≤
      (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) *
        (markedWeightedCoefficientMass P S θ (2 * m) +
          markedWeightedTailCoefficientMass P S θ (2 * m + 1)) +
      ((∫ t in Set.Ioc 0 T, f t) * (harmonic R : ℝ)) *
        (markedWeightedLocalMass P S θ (2 * m) +
          2 * markedWeightedTailModel P S θ (2 * m + 1)) := by
  classical
  let I : ℝ := ∫ t in Set.Ioc 0 T, f t
  let V : ℝ := 3 * ∫ t in Set.Ioc 0 T, |deriv f t|
  let J := markedWeightedIndices P S (2 * m)
  let A := markedWeightedTruncation P S θ (2 * m)
  let D := markedWeightedTail P S θ (2 * m + 1)
  let MA : ℝ := ∑ i ∈ J, markedWeightedCoefficient θ i / (markedWeightedDivisor S i : ℝ)
  let MT := markedWeightedTailModel P S θ (2 * m + 1)
  have hI : 0 ≤ I := integral_nonneg hf0
  have hD (i : MarkedWeightedIndex) (hi : i∈J) :
      0 < markedWeightedDivisor S i ∧ (markedWeightedDivisor S i).Coprime M := by
    refine ⟨markedWeightedDivisor_pos P S hP hS hi,?_⟩
    have hTi := (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hi).2).1
    exact Nat.Coprime.prod_left (fun p hp => hcop p ((Finset.mem_union.mp hp).elim
      (fun h => hS h) (fun h => (Finset.mem_sdiff.mp (hTi h)).1)))
  have hpoly := giantFixedResiduePolynomial_summed_error J (markedWeightedDivisor S)
    (markedWeightedCoefficient θ) M a R hM ha hD f hT hf hderiv hfT
  dsimp only [J] at hpoly
  simp_rw [← markedWeightedTruncation_eq_polynomial] at hpoly
  change (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ giantFixedResidueSet M a r T, f u * A u) - giantFixedResidueScale M r I * MA|) ≤
    (R : ℝ) * V * markedWeightedCoefficientMass P S θ (2 * m) +
      |I| * (harmonic R : ℝ) * markedWeightedLocalMass P S θ (2 * m) at hpoly
  rw [abs_of_nonneg hI] at hpoly
  have hdiv (Q : Finset ℕ) (hQ : Q ∈ (P \ S).powersetCard (2 * m + 1)) :
      0 < ∏ p ∈ S ∪ Q, p := by
    apply Finset.prod_pos
    intro p hp
    exact (hP p (Finset.mem_union.mp hp |>.elim (fun h => hS h)
      (fun h => (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hQ).1 h)).1))).pos
  have hcoef (Q : Finset ℕ) (hQ : Q ∈ (P \ S).powersetCard (2 * m + 1)) :
      0 ≤ ∏ p ∈ Q, θ p := by
    apply Finset.prod_nonneg
    intro p hp
    exact (hθ p (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hQ).1 hp)).1).1
  have htailFull := marked_positive_polynomial_summed_upper R ((P \ S).powersetCard (2 * m + 1))
    (fun Q => ∏ p ∈ S ∪ Q, p) (fun Q => ∏ p ∈ Q, θ p) hdiv hcoef
    f hT hf hderiv hfT hI
  change (∑ r ∈ Finset.Icc 1 R, ∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => r∣u+1), f u*D u) ≤
    (I * (harmonic R : ℝ)) * MT +
      (R : ℝ) * V * markedWeightedTailCoefficientMass P S θ (2 * m + 1) at htailFull
  have hD0 (u : ℕ) : 0≤D u := by
    unfold D markedWeightedTail markedIndexedDivisorPolynomial
    apply Finset.sum_nonneg
    intro Q hQ
    split_ifs
    · exact hcoef Q hQ
    · exact le_rfl
  have htail := (Finset.sum_le_sum fun r (_ : r∈Finset.Icc 1 R) =>
    Finset.sum_le_sum_of_subset_of_nonneg (giantFixedResidueSet_subset M a r T)
      (fun u _ _ => mul_nonneg (hf0 u) (hD0 u))).trans htailFull
  have hmodel : |markedWeightedModel P S θ - MA| ≤ MT :=
    markedWeightedModel_truncation_error P S hP θ hθ m
  have happ (u : ℕ) : |markedWeightedResidual P S θ u - A u| ≤ D u := by
    have h := markedWeightedTruncation_error P S hP hS θ hθ m u
    rw [abs_sub_comm, abs_of_nonneg h.1]
    exact h.2
  have hcomp (r : ℕ) :
      |(∑ u ∈ giantFixedResidueSet M a r T, f u * markedWeightedResidual P S θ u) -
          giantFixedResidueScale M r I * markedWeightedModel P S θ| ≤
        |(∑ u ∈ giantFixedResidueSet M a r T, f u * A u) - giantFixedResidueScale M r I * MA| +
          (∑ u ∈ giantFixedResidueSet M a r T, f u * D u) + giantFixedResidueScale M r I * MT := by
    have h := marked_sum_comparison (giantFixedResidueSet M a r T) (fun u => f u)
      (markedWeightedResidual P S θ) A D (fun u _ => hf0 u) (fun u _ => happ u)
      (c := giantFixedResidueScale M r I) hmodel
    rwa [abs_of_nonneg (giantFixedResidueScale_nonneg M r hI)] at h
  have hMT : 0≤MT := by
    exact Finset.sum_nonneg (fun Q hQ => div_nonneg (hcoef Q hQ) (Nat.cast_nonneg _))
  have hsum : (∑ r∈Finset.Icc 1 R,giantFixedResidueScale M r I*MT) ≤
      (I * (harmonic R : ℝ)) * MT := by
    rw [← Finset.sum_mul,← reciprocal_Icc_eq_harmonic,Finset.mul_sum]
    apply mul_le_mul_of_nonneg_right _ hMT
    exact Finset.sum_le_sum (fun r _ => by
      simpa only [div_eq_mul_inv,one_mul] using giantFixedResidueScale_le M r hM hI)
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 R,
        (|(∑ u ∈ giantFixedResidueSet M a r T, f u * A u) - giantFixedResidueScale M r I * MA| +
          (∑ u ∈ giantFixedResidueSet M a r T, f u * D u) + giantFixedResidueScale M r I * MT) :=
      Finset.sum_le_sum (fun r _ => hcomp r)
    _ = (∑ r ∈ Finset.Icc 1 R,
        |(∑ u ∈ giantFixedResidueSet M a r T, f u * A u) - giantFixedResidueScale M r I * MA|) +
        (∑ r ∈ Finset.Icc 1 R, ∑ u ∈ giantFixedResidueSet M a r T, f u * D u) +
        (∑ r∈Finset.Icc 1 R,giantFixedResidueScale M r I*MT) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ ((R : ℝ) * V * markedWeightedCoefficientMass P S θ (2 * m) +
          I * (harmonic R : ℝ) * markedWeightedLocalMass P S θ (2 * m)) +
        ((I * (harmonic R : ℝ)) * MT +
          (R : ℝ) * V * markedWeightedTailCoefficientMass P S θ (2 * m + 1)) +
        (I * (harmonic R : ℝ)) * MT := add_le_add (add_le_add hpoly htail) hsum
    _ = _ := by dsimp [I, V, MT]; ring

end
end ArtinMatthews
