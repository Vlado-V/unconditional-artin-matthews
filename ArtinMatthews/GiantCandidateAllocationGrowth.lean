module

public import ArtinMatthews.GiantCandidateAllocationCore
public import ArtinMatthews.GiantCandidateSlotError
public import ArtinMatthews.MarkedMajorArcRoughMertens
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The literal invariant core satisfies the divisor-growth condition of
the two-sided argument. The original rough logarithm and Mertens factor
are kept in its finite bound. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

theorem giantOrderedProductFiber_card_le_divisors_pow (j n : ℕ) :
    (giantOrderedProductFiber j n).card ≤ n.divisors.card ^ j := by
  have hsub : giantOrderedProductFiber j n ⊆
      Fintype.piFinset (fun _ : Fin j => n.divisors) := by
    intro t ht
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_finMulAntidiag ht i, (Nat.mem_finMulAntidiag.mp ht).2⟩
  exact (card_le_card hsub).trans_eq (Fintype.card_piFinset_const _ _)

theorem giantCandidateAllocationCore_norm_le (C P : Finset ℕ) {W z : ℝ}
    (hz : 1 < z) (j n : ℕ) :
    ‖giantCandidateAllocationCore C P W z j n‖ ≤
      (giantCandidateSlotBound W z) ^ j * ((giantCandidateStrip P n).divisors.card : ℝ) ^ j := by
  let B := giantCandidateSlotBound W z
  let E := giantOrderedProductFiber j (giantCandidateStrip P n)
  have hB : 0 ≤ B := giantCandidateSlotBound_nonneg hz
  have hcoef (m : ℕ) : ‖giantCandidateStrippedSlotCoefficient C W z m‖ ≤ B := by
    apply (giantCandidateStrippedSlotCoefficient_norm_le_envelope C hz m).trans
    unfold giantCandidateProxyEnvelope
    split_ifs
    · exact le_rfl
    · exact hB
  have hprod (t : Fin j → ℕ) :
      ‖∏ i,giantCandidateStrippedSlotCoefficient C W z (t i)‖ ≤ B ^ j := by
    rw [norm_prod]
    have h := Finset.prod_le_prod₀
      (s := (univ : Finset (Fin j)))
      (fun i _ => norm_nonneg (giantCandidateStrippedSlotCoefficient C W z (t i)))
      (fun i _ => hcoef (t i))
    simpa only [prod_const,card_univ,Fintype.card_fin] using h
  have hcard : (E.card : ℝ) ≤ ((giantCandidateStrip P n).divisors.card : ℝ) ^ j := by
    exact_mod_cast giantOrderedProductFiber_card_le_divisors_pow j (giantCandidateStrip P n)
  unfold giantCandidateAllocationCore
  calc
    _ ≤ ∑ t∈E,‖∏ i,giantCandidateStrippedSlotCoefficient C W z (t i)‖ := norm_sum_le _ _
    _ ≤ ∑ _t∈E,B ^ j := sum_le_sum (fun t _ => hprod t)
    _ = B ^ j * (E.card : ℝ) := by rw [sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcard (pow_nonneg hB j)

theorem giantCandidateSlotBound_actual_le_one (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, 1 < x^γ ∧
      giantCandidateSlotBound (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) ≤ 1 := by
  let E := Real.exp (Real.eulerMascheroniConstant + 1)
  have hlarge := ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1 - 6/25)).comp
    Real.tendsto_log_atTop).eventually (eventually_ge_atTop (E/γ))
  filter_upwards [hlarge,Real.tendsto_log_atTop.eventually
    (marked_rough_density_inverse_cutoff (6/25) (by norm_num)),eventually_gt_atTop (1:ℝ)]
    with x hxLarge hxEuler hx
  let L := Real.log x
  have hL : 0 < L := Real.log_pos hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hz : 1 < x^γ := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow (by norm_num : (0:ℝ) ≤ 1) hx hγ
  change E/γ ≤ L^(1-6/25:ℝ) at hxLarge
  have hmain : E*L^(6/25:ℝ) ≤ γ*L := by
    calc
      _ = γ*(E/γ)*L^(6/25:ℝ) := by field_simp [hγ.ne']
      _ ≤ γ*L^(1-6/25:ℝ)*L^(6/25:ℝ) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hxLarge hγ.le) (Real.rpow_nonneg hL.le _)
      _ = _ := by
        rw [mul_assoc,← Real.rpow_add hL,show (1-6/25:ℝ)+6/25=1 by ring,Real.rpow_one]
  refine ⟨hz,?_⟩
  unfold giantCandidateSlotBound
  apply (div_le_one (Real.log_pos hz)).mpr
  rw [Real.log_rpow hx0]
  exact hxEuler.trans hmain

theorem giantCandidateAllocationCore_actual_growth (γ : ℝ) (hγ : 0 < γ) (j : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ (C P : Finset ℕ) (n : ℕ),
      ‖giantCandidateAllocationCore C P (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j n‖ ≤
        ((giantCandidateStrip P n).divisors.card : ℝ) ^ j := by
  filter_upwards [giantCandidateSlotBound_actual_le_one γ hγ] with x hx
  intro C P n
  apply (giantCandidateAllocationCore_norm_le C P hx.1 j n).trans
  exact mul_le_of_le_one_left (pow_nonneg (Nat.cast_nonneg _) _) 
    (pow_le_one₀ (giantCandidateSlotBound_nonneg hx.1) hx.2)

end
end ArtinMatthews
