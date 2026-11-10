module

public import ArtinMatthews.IdealProductBasis
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

/-! Finite pattern sums use the exact weighted Euclidean norm. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedIdealWeightedVector_sum
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {M : ℕ}
    (s : Finset I) (f : I → MarkedPhysicalMarking P M → ℂ) :
    idealWeightedVector P (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, idealWeightedVector P (f i) := by
  classical
  ext a
  simp [idealWeightedVector, Finset.mul_sum]

theorem giantSignedIdealEnergy_sum
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {M : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (s : Finset I)
    (c : I → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i)
    (f : MarkedPhysicalMarking P M → ℂ) (T : I → MarkedPhysicalMarking P M → ℂ)
    (hT : ∀ i ∈ s, idealLabelEnergy P M (T i) ≤ (c i) ^ 2 * idealLabelEnergy P M f) :
    idealLabelEnergy P M (fun a => ∑ i ∈ s, T i a) ≤
      (∑ i ∈ s, c i) ^ 2 * idealLabelEnergy P M f := by
  classical
  have hi (i : I) (his : i ∈ s) :
      ‖idealWeightedVector P (T i)‖ ≤ c i * ‖idealWeightedVector P f‖ := by
    have he := hT i his
    rw [← idealWeightedVector_norm_sq P hV, ← idealWeightedVector_norm_sq P hV] at he
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (hc i his) (norm_nonneg _))).mp
    nlinarith
  have hn : ‖idealWeightedVector P (fun a => ∑ i ∈ s, T i a)‖ ≤
      (∑ i ∈ s, c i) * ‖idealWeightedVector P f‖ := by
    rw [giantSignedIdealWeightedVector_sum]
    calc
      _ ≤ ∑ i ∈ s, ‖idealWeightedVector P (T i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, c i * ‖idealWeightedVector P f‖ := Finset.sum_le_sum (fun i his => hi i his)
      _ = _ := (Finset.sum_mul s c _).symm
  have hc0 : 0 ≤ (∑ i ∈ s, c i) * ‖idealWeightedVector P f‖ :=
    mul_nonneg (Finset.sum_nonneg hc) (norm_nonneg _)
  have hs := (sq_le_sq₀ (norm_nonneg _) hc0).mpr hn
  rw [idealWeightedVector_norm_sq P hV] at hs
  rw [← idealWeightedVector_norm_sq P hV (f := f)]
  nlinarith

end
end ArtinMatthews
