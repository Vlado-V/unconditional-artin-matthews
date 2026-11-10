module

public import ArtinMatthews.GiantTwoSidedRawSharedAggregation
public import ArtinMatthews.GiantCandidateGroups
public import ArtinMatthews.GiantCandidateSelectedGroups
public import ArtinMatthews.GiantTwoSidedSharedRestorationActual
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The harmonic restoration estimate passes through both literal free
label sums and the complex position kernel with its original phase. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedNormalizedMarkWeight_error {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (k w : ℕ) {q δ : ℝ} (hq : 0 ≤ q)
    (h : ∀ (b : GiantTwoSidedFreeMarking P w) (b' : GiantTwoSidedFreeMarking P (w+1)),
      ‖giantTwoSidedSharedNormalizedDamping k q w b.val b'.val -
        giantTwoSidedOneMarkDampingProduct P q w‖ ≤
          δ*giantTwoSidedOneMarkDampingProduct P q w) :
    ‖giantTwoSidedNormalizedMarkWeight P k q w -
      giantCandidateActiveOneMark P q w*giantCandidateActiveOneMark P q (w+1)‖ ≤
        δ*(giantCandidateActiveOneMark P q w*giantCandidateActiveOneMark P q (w+1)) := by
  let B := (∏ j,(bandReciprocalMass (P j))⁻¹)^2
  let D := giantTwoSidedOneMarkDampingProduct P q w
  let f (b : GiantTwoSidedFreeMarking P w) (b' : GiantTwoSidedFreeMarking P (w+1)) :=
    giantTwoSidedSharedNormalizedDamping k q w b.val b'.val
  let M := giantCandidateActiveOneMark P q w*giantCandidateActiveOneMark P q (w+1)
  have hsum : B*(∑ _b : GiantTwoSidedFreeMarking P w,
      ∑ _b' : GiantTwoSidedFreeMarking P (w+1),D) = M := by
    dsimp only [M]
    rw [← giantTwoSidedFreeMarking_pair_weight_eq P hdis w hq]
    simp only [sum_const, nsmul_eq_mul, card_univ, B, D]
    ring
  have hB : 0 ≤ B := sq_nonneg _
  change ‖B*(∑ b,∑ b', f b b')-M‖ ≤ δ*M
  rw [← hsum,← mul_sub,norm_mul,Real.norm_eq_abs B,abs_of_nonneg hB]
  calc
    _ ≤ B*(∑ b,∑ b',‖f b b'-D‖) := by
      simp_rw [← sum_sub_distrib]
      apply mul_le_mul_of_nonneg_left _ hB
      exact (norm_sum_le _ _).trans (sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ B*(∑ _b : GiantTwoSidedFreeMarking P w,
        ∑ _b' : GiantTwoSidedFreeMarking P (w+1),δ*D) :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun b _ => sum_le_sum fun b' _ => h b b') hB
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_univ]; ring

theorem giantCandidateNormalizedMarkWeight_log_saving (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ (S : Finset (GiantCandidateGroupIndex x)) (w : ℕ),
      w∈Ioc 0 ⌊T*x⌋₊ →
      let P (i : S) := giantCandidateGroup x i.val
      ‖giantTwoSidedNormalizedMarkWeight P k q w -
        giantCandidateActiveOneMark P q w*giantCandidateActiveOneMark P q (w+1)‖ ≤
        (Real.log x)^(-A)*(giantCandidateActiveOneMark P q w*giantCandidateActiveOneMark P q (w+1)) := by
  filter_upwards [giantCandidateSharedNormalizedDamping_log_saving k T hT hq hq1 A,
    giantCandidateSelectedGroups_geometry_eventually] with x hr hg
  intro S w hw
  exact giantTwoSidedNormalizedMarkWeight_error _ (hg S).1 k w hq.le
    (fun b b' => hr S w hw b.val b'.val b.property b'.property)

theorem giantTwoSidedRawHarmonic_sum_error {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (k N : ℕ) (q δ : ℝ) (K : ℕ → ℂ)
    (h : ∀ w ∈ Ioc 0 N,
      ‖giantTwoSidedNormalizedMarkWeight P k q w -
        giantCandidateActiveOneMark P q w*giantCandidateActiveOneMark P q (w+1)‖ ≤
          δ*(giantCandidateActiveOneMark P q w*giantCandidateActiveOneMark P q (w+1))) :
    ‖(∑ w ∈ Ioc 0 N,K w*(giantTwoSidedNormalizedMarkWeight P k q w:ℂ)) -
      ∑ w ∈ Ioc 0 N,K w*((giantCandidateActiveOneMark P q w*
        giantCandidateActiveOneMark P q (w+1):ℝ):ℂ)‖ ≤
      δ*(∑ w ∈ Ioc 0 N,‖K w‖*(giantCandidateActiveOneMark P q w*
        giantCandidateActiveOneMark P q (w+1))) := by
  rw [← sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun w hw => ?_)
  rw [← mul_sub,← Complex.ofReal_sub,norm_mul,Complex.norm_real]
  rw [mul_left_comm δ]
  exact mul_le_mul_of_nonneg_left (h w hw) (norm_nonneg _)

end
end ArtinMatthews
