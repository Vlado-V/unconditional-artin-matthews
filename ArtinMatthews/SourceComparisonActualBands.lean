module

public import ArtinMatthews.GiantCandidateSelectedGroups
public import ArtinMatthews.GiantPrimeNormalization
public import ArtinMatthews.GiantPrimeInvariance
public import ArtinMatthews.GiantWindowArithmetic
public import ArtinMatthews.MarkedBonferroniTail
public import ArtinMatthews.MarkedEstimateActualModel
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedProgressionGrowth
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

/-! The combined source bands consist of the fixed inert bands and any
injectively selected family of the literal active groups. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Topology
noncomputable section

universe u v
variable {J : Type u} [Fintype J] {G : Type v} [Fintype G]

def sourceComparisonActualBands (e : J → ℝ) (x : ℝ) (i : G ↪ GiantCandidateGroupIndex x) :
    J ⊕ G → Finset ℕ :=
  Sum.elim (fun j => markedLogPowerBand (e j) x) (giantCandidateGroup x ∘ i)

theorem sourceComparisonActualBands_geometry_eventually (e : J → ℝ)
    (he : ∀ j, (1/10 : ℝ) < e j ∧ e j < 1/5) (heinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, ∀ {G : Type v} [Fintype G] (i : G ↪ GiantCandidateGroupIndex x),
      let P := sourceComparisonActualBands e x i
      Pairwise (fun g h => Disjoint (P g) (P h)) ∧
      (∀ g, Real.log 2 / 2 < bandReciprocalMass (P g) ∧ bandReciprocalMass (P g) < 1) ∧
      (∀ p ∈ univ.biUnion P, p.Prime ∧ Real.exp ((Real.log x) ^ (1/10:ℝ)) ≤ (p : ℝ) ∧
        (p : ℝ) ≤ Real.exp ((Real.log x) ^ (46/100:ℝ))) ∧
      (Fintype.card (J ⊕ G) : ℝ) ≤
        ((Fintype.card J : ℝ) + giantCandidateGroupLogRate) * Real.log (Real.log x) := by
  have hv := eventually_all.mpr (fun j =>
    marked_log_power_band_mass_eventually (show 0 < e j from (by norm_num : (0:ℝ) < 1/10).trans (he j).1))
  have hgap := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8/100)).comp
    Real.tendsto_log_atTop).eventually (eventually_gt_atTop (2:ℝ))
  have hloglog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hv, hgap, hloglog, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    marked_array_disjoint_eventually e heinj, giantCandidateGroup_mass_eventually,
    giantCandidateGroup_total_count_eventually] with x hv hxgap hll hx hlog hji hvi hc
  intro G _ i
  let P := sourceComparisonActualBands e x i
  let L := Real.log x
  have hL : 0 < L := Real.log_pos hx
  have hg : 2 * L ^ (1/5:ℝ) < L ^ (28/100:ℝ) := by
    rw [show (28/100:ℝ) = 1/5 + 8/100 by norm_num, Real.rpow_add hL, mul_comm (2:ℝ)]
    exact mul_lt_mul_of_pos_left hxgap (Real.rpow_pos_of_pos hL _)
  have hInert (j : J) (p : ℕ) (hp : p ∈ markedLogPowerBand (e j) x) :
      p.Prime ∧ Real.exp (L ^ (1/10:ℝ)) ≤ (p : ℝ) ∧
        (p : ℝ) < Real.exp (L ^ (28/100:ℝ)) := by
    obtain ⟨hP, hlo, hhi⟩ := mem_markedLogPowerBand.mp hp
    refine ⟨hP, (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hlog (he j).1.le)).trans hlo, ?_⟩
    exact hhi.trans_lt (Real.exp_lt_exp.mpr ((mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog (he j).2.le) (by norm_num)).trans_lt hg))
  have hActive (g : G) (p : ℕ) (hp : p ∈ giantCandidateGroup x (i g)) :=
    giantCandidateFullPrimes_range hx hlog (mem_giantCandidateFullPrimes.mpr ⟨i g, hp⟩)
  have hIA (j : J) (g : G) : Disjoint (P (.inl j)) (P (.inr g)) := by
    apply disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge (hActive g p hq).2.1) (hInert j p hp).2.2
  have hdis : Pairwise (fun g h => Disjoint (P g) (P h)) := by
    intro g h hne
    rcases g with g | g <;> rcases h with h | h
    · exact hji (fun he => hne (congrArg Sum.inl he))
    · exact hIA g h
    · exact (hIA h g).symm
    · exact giantCandidateGroup_pairwise_disjoint hx hlog
        (fun he => hne (congrArg Sum.inr (i.injective he)))
  have hm (g : J ⊕ G) : Real.log 2 / 2 < bandReciprocalMass (P g) ∧
      bandReciprocalMass (P g) < 1 := by
    cases g with
    | inl j => exact hv j
    | inr g => exact hvi (i g)
  have hp (p : ℕ) (hp : p ∈ univ.biUnion P) : p.Prime ∧
      Real.exp (L ^ (1/10:ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L ^ (46/100:ℝ)) := by
    obtain ⟨g, _, hpg⟩ := mem_biUnion.mp hp
    rcases g with j | g
    · obtain ⟨hP, hlo, hhi⟩ := hInert j p hpg
      exact ⟨hP, hlo, hhi.le.trans (Real.exp_le_exp.mpr
        (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)))⟩
    · obtain ⟨hP, hlo, hhi⟩ := hActive g p hpg
      exact ⟨hP, (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num))).trans hlo,
        hhi.le.trans (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)))⟩
  refine ⟨hdis, hm, hp, ?_⟩
  rw [Fintype.card_sum, Nat.cast_add, add_mul]
  change 1 ≤ Real.log (Real.log x) at hll
  exact add_le_add (le_mul_of_one_le_right (Nat.cast_nonneg _) hll)
    ((Nat.cast_le.mpr (Fintype.card_le_of_injective i i.injective)).trans hc)

theorem sourceComparisonActualBands_long_eventually (e : J → ℝ)
    (he : ∀ j, (1/10 : ℝ) < e j ∧ e j < 1/5) (heinj : Function.Injective e)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ {G : Type v} [Fintype G] (i : G ↪ GiantCandidateGroupIndex x),
      let P := sourceComparisonActualBands e x i
      let Λ := giantPrimeWindow x ε
      (∀ p ∈ Λ, p.Prime) ∧ Disjoint Λ (univ.biUnion P) ∧
      ((Λ.card : ℝ) ≤ x ^ (1 - ε/2)) ∧
      (0 ≤ giantPrimeReciprocalSum x ε ∧ giantPrimeReciprocalSum x ε ≤ 1) ∧
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ (Real.log x) ^ C →
        ∀ p ∈ univ.biUnion P ∪ Λ, p.Coprime k := by
  have hlarge : ∀ᶠ L : ℝ in atTop, L ^ C < Real.exp (L ^ (1/10:ℝ)) := by
    have h := rpow_mul_exp_neg_rpow_tendsto C (by norm_num : (0:ℝ) < 1/10) zero_lt_one
    filter_upwards [h.eventually (gt_mem_nhds zero_lt_one)] with L hL
    simp only [one_mul, neg_mul, Real.exp_neg, ← div_eq_mul_inv] at hL
    exact (div_lt_iff₀ (Real.exp_pos _)).mp hL |>.trans_eq (one_mul _)
  filter_upwards [sourceComparisonActualBands_geometry_eventually.{u, v} e he heinj,
    giant_window_structure_eventually e (fun j => (he j).2.trans (by norm_num))
      (by norm_num : (46/100:ℝ) < 1) hε hεq,
    giantPrimeReciprocalSum_bounds_eventually hε hεq,
    marked_sublinear_log_exp_le_rpow_eventually (46/100) 1 (1-ε) (by norm_num) (by linarith),
    Real.tendsto_log_atTop.eventually hlarge,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with x hG hΛ hCx hsep hlarge hlog hx
  intro G _ i
  let P := sourceComparisonActualBands e x i
  let Λ := giantPrimeWindow x ε
  have hP := (hG i).2.2.1
  have hlo (p : ℕ) (hp : p ∈ Λ) : x ^ (1 - ε) < (p : ℝ) :=
    ((mem_giantPrimeWindow (by linarith : 0 ≤ x)).mp hp).2.1
  have hsep' : Real.exp ((Real.log x) ^ (46/100:ℝ)) ≤ x ^ (1-ε) := by
    simpa only [one_mul] using hsep
  refine ⟨hΛ.1, disjoint_left.mpr (fun p hp hq => (not_lt_of_ge ((hP p hq).2.2.trans hsep')) (hlo p hp)),
    hΛ.2.2.2.1, hCx, ?_⟩
  intro k hk hkx p hp
  have hlarge' : (Real.log x) ^ C < Real.exp ((Real.log x) ^ (1/10:ℝ)) := hlarge
  have hpp : p.Prime ∧ (k : ℝ) < (p : ℝ) := by
    rcases mem_union.mp hp with hp | hp
    · exact ⟨(hP p hp).1, (hkx.trans_lt hlarge').trans_le (hP p hp).2.1⟩
    · exact ⟨hΛ.1 p hp, ((hkx.trans_lt hlarge').trans_le (Real.exp_le_exp.mpr
        (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)))).trans_le (hΛ.2.2.1 p hp)⟩
  exact hpp.1.coprime_iff_not_dvd.mpr (fun hd =>
    (not_lt_of_ge (Nat.cast_le.mpr (Nat.le_of_dvd hk hd))) hpp.2)

end
end ArtinMatthews
