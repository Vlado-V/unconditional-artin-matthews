module

public import ArtinMatthews.GiantTwoSidedPhysicalFamilyMatrix
public import ArtinMatthews.GiantTwoSidedExpandedRootTransfer
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Expanding the physical matrix entries gives the original root-path
statistic with exactly one state mass and both slot averages at each edge. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedExpandedPhysicalMoment_matrix_paths {I J : Type*}
    [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell n : ℕ}
    (patterns : Fin n → Finset I) (C : Fin n → I → J → Finset (Fin k))
    (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i p, GiantTwoSidedPatternCoefficient P (C i p) ell) (roots Z : Finset ℕ) :
    giantTwoSidedExpandedPhysicalMoment patterns C step q ζ K roots Z =
      ∑ s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z,
        (if (s 0).val.1.val ∈ roots ∧ (s (Fin.last n)).val.1.val = (s 0).val.1.val
          then (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) : ℂ) else 0) *
        ∏ i : Fin n, giantTwoSidedPhysicalFamilyMatrix (patterns i) (C i) (step i) q (ζ i) (K i)
          (s i.castSucc) (s i.succ) := by
  let State := GiantTwoSidedEndpointState P (k+ell) Z
  let Choice (i : Fin n) := GiantTwoSidedResidueEdgeChoice (P := P) (patterns i) (C i) ell
  let a : ℂ := giantTwoSidedResidueSlotNormalization (J := J) (k+ell)
  let gate (s : Fin (n+1) → State) : ℂ :=
    if (s 0).val.1.val ∈ roots ∧ (s (Fin.last n)).val.1.val = (s 0).val.1.val then
      (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) : ℂ) else 0
  let F (s : Fin (n+1) → State) (i : Fin n) (c : Choice i) : ℂ :=
    giantTwoSidedPhysicalChoiceCoefficient (step i) q (ζ i) (K i) c (s i.castSucc) (s i.succ)
  have hprod (s : Fin (n+1) → State) :
      (∏ i : Fin n, giantTwoSidedPhysicalFamilyMatrix (patterns i) (C i) (step i) q (ζ i) (K i)
        (s i.castSucc) (s i.succ)) = a^n * ∑ c : (i : Fin n) → Choice i, ∏ i, F s i (c i) := by
    change (∏ i, a * ∑ c : Choice i, F s i c) = _
    rw [Finset.prod_mul_distrib, Fintype.prod_sum]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    _ = a^n * ∑ c : (i : Fin n) → Choice i, ∑ s : Fin (n+1) → State,
          gate s * ∏ i, F s i (c i) := by
      unfold giantTwoSidedExpandedPhysicalMoment giantTwoSidedPhysicalMoment
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : (s 0).val.1.val ∈ roots
      · simp only [h, true_and, ite_true, gate, F, giantTwoSidedPhysicalChoiceCoefficient]
      · simp only [h, false_and, ite_false, zero_mul, gate]
    _ = ∑ s : Fin (n+1) → State, a^n * ∑ c : (i : Fin n) → Choice i,
          gate s * ∏ i, F s i (c i) := by rw [Finset.sum_comm, Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [hprod, ← Finset.mul_sum]
      change _ = gate s * _
      ring

end
end ArtinMatthews
