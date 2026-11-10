module

public import ArtinMatthews.GiantCandidateGroups
public import ArtinMatthews.GiantTwoSidedPatternKernel
public import ArtinMatthews.GiantComparisonStripLabels
public import ArtinMatthews.GiantTwoSidedPatternDilationBound
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Every actual auxiliary product is positive and bounded by the
full source dilation. Its exact row scale is therefore at most x². -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section

theorem giantCandidateComparisonAuxiliaryScale_eventually (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x))
      (C : S → Finset (Fin k))
      (aux : GiantTwoSidedPatternAuxiliary (fun g : S => giantCandidateGroup x g.val) C),
      let d := giantTwoSidedPatternAuxiliaryProduct aux
      0 < d ∧ (d:ℝ) ≤ x ∧ 1 ≤ x*(d:ℝ) ∧ x*(d:ℝ) ≤ x^2 := by
  filter_upwards [giantCandidatePatternDilation_subpower k (δ:=1) zero_lt_one,
    giantCandidateSelectedGroups_geometry_eventually, giantCandidateFullPrimes_prime_upper_eventually,
    eventually_gt_atTop (1:ℝ)] with x hD hgeo hprime hx
  intro S C aux
  dsimp only
  let P (g : S) := giantCandidateGroup x g.val
  let d := giantTwoSidedPatternAuxiliaryProduct aux
  have hP (g : S) (p : ℕ) (hp : p ∈ P g) : p.Prime :=
    (hprime p (mem_giantCandidateFullPrimes.mpr ⟨g.val,hp⟩)).1
  have hV (g : S) : 0 < bandReciprocalMass (P g) :=
    (div_pos (Real.log_pos (by norm_num)) (by norm_num)).trans ((hgeo S).2.1 g).1
  have hne (g : S) : Nonempty ↥(P g) := by
    by_contra h
    have h0 : P g = ∅ := eq_empty_iff_forall_notMem.mpr (fun p hp => h ⟨⟨p,hp⟩⟩)
    simpa [bandReciprocalMass,h0] using hV g
  let labels : MarkedPhysicalMarking P (k+1) := fun g _ => Classical.choice (hne g)
  have hb := hD S 1 C labels aux
  rw [Real.rpow_one,giantTwoSidedPatternDilation] at hb
  have hR : 1 ≤ giantTwoSidedPatternCopiedProduct C labels := by
    rw [← giantComparisonSharedProduct_eq_copied]
    exact giantComparisonSharedProduct_pos hP _
  have hdpos : 0 < d := prod_pos fun g _ => prod_pos fun i _ => (hP g _ (aux g i).property).pos
  have hd : (d:ℝ) ≤ x := by
    have hle : d ≤ giantTwoSidedPatternCopiedProduct C labels*d := by
      simpa only [one_mul] using Nat.mul_le_mul_right d hR
    exact (Nat.cast_le.mpr hle).trans hb
  refine ⟨hdpos,hd,?_,?_⟩
  · exact one_le_mul_of_one_le_of_one_le hx.le (Nat.one_le_cast.mpr hdpos)
  · rw [pow_two]
    exact mul_le_mul_of_nonneg_left hd (zero_lt_one.trans hx).le

end
end ArtinMatthews
