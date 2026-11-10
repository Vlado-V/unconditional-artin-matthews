module

public import ArtinMatthews.GiantCandidateGroups
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! A performed active subset inherits the actual candidate geometry.
Any fixed exponential in the number of its groups is a fixed logarithmic
power, as required for the finite success-factor expansion. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

def giantCandidateGroupLogRate : ℝ := (12/100)/Real.log 2

theorem giantCandidateGroup_total_count_eventually :
    ∀ᶠ x : ℝ in atTop,
      (Fintype.card (GiantCandidateGroupIndex x):ℝ) ≤
        giantCandidateGroupLogRate * Real.log (Real.log x) := by
  filter_upwards [giantCandidateGroup_counts_eventually] with x hx
  have h := add_le_add hx.2.1 hx.2.2.2
  calc
    _ = (Fintype.card (GiantCandidateSmallGroupIndex x):ℝ) +
        (Fintype.card (GiantCandidateBigGroupIndex x):ℝ) := by
      rw [Fintype.card_sum,Nat.cast_add]
    _ ≤ _ := h
    _ = _ := by unfold giantCandidateGroupLogRate; ring

theorem giantCandidateSelectedGroups_union_subset {x : ℝ}
    (S : Finset (GiantCandidateGroupIndex x)) :
    univ.biUnion (fun i : S => giantCandidateGroup x i.val) ⊆ giantCandidateFullPrimes x := by
  intro p hp
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
  exact mem_giantCandidateFullPrimes.mpr ⟨i.val,hi⟩

theorem giantCandidateSelectedGroups_geometry_eventually :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      Pairwise (fun i j : S => Disjoint (giantCandidateGroup x i.val)
        (giantCandidateGroup x j.val)) ∧
      (∀ i : S, Real.log 2/2 < bandReciprocalMass (giantCandidateGroup x i.val) ∧
        bandReciprocalMass (giantCandidateGroup x i.val) < 1) ∧
      univ.biUnion (fun i : S => giantCandidateGroup x i.val) ⊆ giantCandidateFullPrimes x := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    giantCandidateGroup_mass_eventually] with x hx hlog hmass
  intro S
  exact ⟨fun _ _ hij => giantCandidateGroup_pairwise_disjoint hx hlog
    (fun he => hij (Subtype.ext he)),fun i => hmass i.val,giantCandidateSelectedGroups_union_subset S⟩

theorem giantCandidateSelectedGroups_exponential_cost_eventually (B : ℝ) (hB : 1 ≤ B) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      B^S.card ≤ (Real.log x)^(giantCandidateGroupLogRate * Real.log B) := by
  filter_upwards [giantCandidateGroup_total_count_eventually,eventually_gt_atTop (1:ℝ)] with x hx hxp
  intro S
  have hcard : (S.card:ℝ) ≤ giantCandidateGroupLogRate * Real.log (Real.log x) :=
    (Nat.cast_le.mpr (card_le_univ S)).trans hx
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  calc
    _ = Real.exp (Real.log B * (S.card:ℝ)) := by
      rw [← Real.rpow_natCast,Real.rpow_def_of_pos hB0]
    _ ≤ Real.exp (Real.log B * (giantCandidateGroupLogRate * Real.log (Real.log x))) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcard (Real.log_nonneg hB))
    _ = _ := by
      rw [Real.rpow_def_of_pos (Real.log_pos hxp)]
      congr 1
      ring

end
end ArtinMatthews
