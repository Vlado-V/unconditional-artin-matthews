module

public import ArtinMatthews.GiantCandidateGroups
public import ArtinMatthews.GiantComparisonSharedCollision
public import ArtinMatthews.GiantCandidateSelectedGroups
public import ArtinMatthews.GiantComparisonSharedCollisionActual
public import ArtinMatthews.MarkedBonferroniTail
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

/-! The actual copied collision loss, including both inverse damping
powers, decays faster than every fixed inverse logarithmic power. -/
namespace ArtinMatthews
open Finset Filter Set
open scoped BigOperators Topology
noncomputable section

theorem giantComparisonAuxiliarySlots_card_le {J : Type*} [Fintype J]
    {k : ℕ} (C : J → Finset (Fin k)) :
    Fintype.card (Σ g : J, ↥(C g)) ≤ k*Fintype.card J := by
  rw [Fintype.card_sigma, show k*Fintype.card J = ∑ _g : J,k by simp [Nat.mul_comm]]
  apply sum_le_sum
  intro g _
  simpa only [Fintype.card_coe, card_univ, Fintype.card_fin] using Finset.card_le_card (subset_univ (C g))

theorem giantCandidateComparisonSharedLoss_eventually (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x))
      (C : S → Finset (Fin k))
      (aux : GiantTwoSidedPatternAuxiliary (fun g : S => giantCandidateGroup x g.val) C)
      (w w' : ℕ), 0 < w → 0 < w' → (w:ℝ) ≤ x^T → (w':ℝ) ≤ x^T →
      ((q⁻¹)^(2*(k*Fintype.card S))+1)*giantComparisonSharedBadMass aux w w' ≤ (Real.log x)^(-A) := by
  obtain ⟨B,hB,hbad⟩ := giantCandidateComparisonSharedBadMass_eventually k T hT
  let K := (q⁻¹)^(2*k)
  let c := giantCandidateGroupLogRate*Real.log K
  have hK : 1 ≤ K := one_le_pow₀ ((one_le_inv₀ hq).mpr hq1)
  have hc : 0 ≤ c := mul_nonneg (by unfold giantCandidateGroupLogRate; positivity) (Real.log_nonneg hK)
  have ht := ((rpow_mul_exp_neg_rpow_tendsto (c+2+A)
    (by norm_num : (0:ℝ)<27/100) (by norm_num : (0:ℝ)<1)).comp
      Real.tendsto_log_atTop).const_mul (2*B)
  simp only [Function.comp_def,neg_one_mul,mul_zero] at ht
  filter_upwards [hbad,giantCandidateSelectedGroups_exponential_cost_eventually K hK,
    Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ),
    ht.eventually (Iio_mem_nhds (zero_lt_one : (0:ℝ)<1))]
    with x hb hcost hL hsmall
  intro S C aux w w' hw hw' hwT hw'T
  let L := Real.log x
  let R := (q⁻¹)^(2*(k*Fintype.card S))
  let E := Real.exp (-(L^(27/100:ℝ)))
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hR : R ≤ L^c := by
    unfold R
    rw [← Nat.mul_assoc,pow_mul,Fintype.card_coe]
    exact hcost S
  have hR1 : R+1 ≤ 2*L^c := by linarith only [hR,Real.one_le_rpow hL hc]
  have hpows : L^(c+2+A)*L^(-A) = L^c*L^2 := by
    rw [← Real.rpow_add hL0,show c+2+A+(-A)=c+2 by ring,Real.rpow_add hL0,Real.rpow_two]
  change (R+1)*giantComparisonSharedBadMass aux w w' ≤ L^(-A)
  calc
    _ ≤ (R+1)*(B*L^2*E) := mul_le_mul_of_nonneg_left (hb S C aux w w' hw hw' hwT hw'T) (by unfold R; positivity)
    _ ≤ (2*L^c)*(B*L^2*E) := mul_le_mul_of_nonneg_right hR1 (by positivity)
    _ = (2*B*E)*(L^c*L^2) := by ring
    _ = (2*B*(L^(c+2+A)*E))*L^(-A) := by rw [← hpows]; ring
    _ ≤ 1*L^(-A) := mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_nonneg hL0.le _)
    _ = _ := one_mul _

end
end ArtinMatthews
