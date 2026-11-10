module

public import ArtinMatthews.CircleVoronoiModulus
public import ArtinMatthews.CircleNormalizerDefinitions
public import ArtinMatthews.CircleWeightedAverage
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Exact averaging of the individual-modulus double Voronoi identities
with the actual admissible modulus family and its totient normalizer. -/

noncomputable section
open Complex UpperHalfPlane Set
open scoped MatrixGroups ContDiff BigOperators
namespace ArtinMatthews

theorem circleDetector_filtered_sum_eq_average {ι : Type*}
    (S : Finset ι) (A : ι → ℂ) (frequency : ι → ℤ)
    (p : ι → Prop) [DecidablePred p] (Q : Finset ℕ) (weight : ℕ → ℝ) :
    (∑ k ∈ S.filter p, A k * circleDetector Q weight (frequency k)) =
      (∑ q ∈ Q, (weight q : ℂ) * (∑ k ∈ S,
        A k * primitiveCircleSum q (frequency k) * (if p k then 1 else 0))) /
          (circleNormalizer Q weight : ℂ) := by
  rw [circleDetector_sum_eq_average]
  simp only [Finset.sum_filter, mul_ite, mul_one, mul_zero]

theorem circle_weightOne_voronoi_average
    (N : ℕ) [NeZero N] (hN : 3 ∣ N) (f : CuspForm (cubicThetaKernel N) 1)
    (m1 m2 K1 K2 : ℕ)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hne : m1 ≠ m2)
    (hsq1 : Squarefree m1) (hsq2 : Squarefree m2)
    (Q : Finset ℕ) (weight : ℕ → ℝ) (hpos : ∀ q ∈ Q, 0 < q)
    (hQ : ∀ q ∈ Q, N * (shiftedCommonPrimePart m1 m2)^2 ∣ q)
    (hc : ∀ q ∈ Q, ((m1 / (m1.gcd m2)) * (m2 / (m1.gcd m2))).Coprime q)
    (H1 H2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ H1) (hs2 : ContDiff ℝ ∞ H2)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hv1 : v1 ≤ K1) (hv2 : v2 ≤ K2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2) :
    (∑ k ∈ ((Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2)).filter
        (fun k => ((m1.gcd m2) : ℤ) ∣ ((k.1 : ℤ) - 1)),
      cuspSourcePair f H1 H2 k * circleDetector Q weight
        (circleShiftedFrequency (m1 / (m1.gcd m2)) (m2 / (m1.gcd m2)) k)) =
      (∑ q ∈ Q, (weight q : ℂ) * circleVoronoiDual N f m1 m2 q H1 H2) /
        (circleNormalizer Q weight : ℂ) := by
  rw [circleDetector_filtered_sum_eq_average]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [circle_weightOne_voronoi_modulus N hN f m1 m2 q K1 K2 (hpos q hq)
    hm1 hm2 hne hsq1 hsq2 (hQ q hq) (hc q hq)
    H1 H2 hs1 hs2 u1 v1 u2 v2 hu1 hu2 hv1 hv2 hw1 hw2]

theorem circle_weightOne_voronoi_admissible
    (N : ℕ) [NeZero N] (hN : 3 ∣ N) (f : CuspForm (cubicThetaKernel N) 1)
    (m1 m2 K1 K2 L : ℕ) (hL : 0 < L)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hne : m1 ≠ m2)
    (hsq1 : Squarefree m1) (hsq2 : Squarefree m2) (weight : ℕ → ℝ)
    (H1 H2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ H1) (hs2 : ContDiff ℝ ∞ H2)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hv1 : v1 ≤ K1) (hv2 : v2 ≤ K2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2) :
    let F := N * (shiftedCommonPrimePart m1 m2)^2
    let r := (m1 / (m1.gcd m2)) * (m2 / (m1.gcd m2))
    let Q := circleModuli F r L
    (∑ k ∈ ((Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2)).filter
        (fun k => ((m1.gcd m2) : ℤ) ∣ ((k.1 : ℤ) - 1)),
      cuspSourcePair f H1 H2 k * circleDetector Q weight
        (circleShiftedFrequency (m1 / (m1.gcd m2)) (m2 / (m1.gcd m2)) k)) =
      (∑ q ∈ Q, (weight q : ℂ) * circleVoronoiDual N f m1 m2 q H1 H2) /
        (circleNormalizer Q weight : ℂ) := by
  intro F r Q
  apply circle_weightOne_voronoi_average N hN f m1 m2 K1 K2 hm1 hm2 hne hsq1 hsq2 Q weight
    ?_ ?_ ?_ H1 H2 hs1 hs2 u1 v1 u2 v2 hu1 hu2 hv1 hv2 hw1 hw2
  · intro q hq
    have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    omega
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.2.symm

end ArtinMatthews
