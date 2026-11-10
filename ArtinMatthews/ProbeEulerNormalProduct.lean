module

public import ArtinMatthews.ProbeEulerLocalHolomorphy
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
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

/-! Normal convergence of the actual ideal-prime rational correction
product, with an absolutely convergent principal logarithm and no zeros.
All bounds hold on both enlarged source-05 regions. -/

namespace ArtinMatthews

noncomputable section
open NumberField IsDedekindDomain Set Filter
open scoped NumberField Classical BigOperators Topology

variable (K : Type*) [Field K] [NumberField K]

def probeEulerLogMajorant (S : Finset (ProbePrime K)) : ℝ :=
  ∑' P : ProbeGoodPrime K S, 240 * probePrimeWeight K P.val

def probeEulerLog (S : Finset (ProbePrime K)) (a b c : ProbePrime K → ℂ)
    (p : ProbeCoordinates) : ℂ :=
  ∑' P : ProbeGoodPrime K S, probePrimeLog K a b c P.val p

def probeEulerProduct (S : Finset (ProbePrime K)) (a b c : ProbePrime K → ℂ)
    (p : ProbeCoordinates) : ℂ :=
  ∏' P : ProbeGoodPrime K S, probePrimeCorrection K a b c P.val p

theorem probeEulerLogMajorant_nonneg (S : Finset (ProbePrime K)) :
    0 ≤ probeEulerLogMajorant K S :=
  tsum_nonneg fun P => mul_nonneg (by norm_num) (probePrimeWeight_nonneg K P.val)

theorem probePrimeCorrection_sub_one_norm_summable (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    Summable (fun P : ProbeGoodPrime K S => ‖probePrimeCorrection K a b c P.val p - 1‖) :=
  (((probePrimeWeight_summable K).subtype (fun P => P ∉ S)).mul_left 160).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun P => probePrimeCorrection_norm_sub_one_le K a b c ha hb hc S hS P hp)

theorem probePrimeLog_norm_summable (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    Summable (fun P : ProbeGoodPrime K S => ‖probePrimeLog K a b c P.val p‖) :=
  (probeGoodPrime_majorant_summable K S).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => probePrimeLog_norm_le K a b c ha hb hc S hS P hp)

theorem probePrimeLog_summable (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    Summable (fun P : ProbeGoodPrime K S => probePrimeLog K a b c P.val p) :=
  Summable.of_norm_bounded (probeGoodPrime_majorant_summable K S)
    (fun P => probePrimeLog_norm_le K a b c ha hb hc S hS P hp)

theorem probeEulerLog_norm_le (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    ‖probeEulerLog K S a b c p‖ ≤ probeEulerLogMajorant K S :=
  tsum_of_norm_bounded (probeGoodPrime_majorant_summable K S).hasSum
    (fun P => probePrimeLog_norm_le K a b c ha hb hc S hS P hp)

theorem probeEulerLog_tendstoUniformlyOn (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1) :
    TendstoUniformlyOn
      (fun T : Finset (ProbeGoodPrime K S) => fun p =>
        ∑ P ∈ T, probePrimeLog K a b c P.val p)
      (probeEulerLog K S a b c) atTop probeEulerDomain :=
  tendstoUniformlyOn_tsum (probeGoodPrime_majorant_summable K S)
    (fun P _ hp => probePrimeLog_norm_le K a b c ha hb hc S hS P hp)

theorem probeEulerProduct_hasProd (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    HasProd (fun P : ProbeGoodPrime K S => probePrimeCorrection K a b c P.val p)
      (Complex.exp (probeEulerLog K S a b c p)) := by
  have H := (probePrimeLog_summable K S hS a b c ha hb hc hp).hasSum.cexp
  simpa only [Function.comp_def, probeEulerLog, probePrimeLog, Complex.exp_log
    (probePrimeCorrection_ne_zero K a b c ha hb hc S hS _ hp)] using H

theorem probeEulerProduct_eq_exp (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    probeEulerProduct K S a b c p = Complex.exp (probeEulerLog K S a b c p) :=
  (probeEulerProduct_hasProd K S hS a b c ha hb hc hp).tprod_eq

theorem probeEulerProduct_ne_zero (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    probeEulerProduct K S a b c p ≠ 0 := by
  rw [probeEulerProduct_eq_exp K S hS a b c ha hb hc hp]
  exact Complex.exp_ne_zero _

theorem probeEulerProduct_hasProdUniformlyOn (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1) :
    HasProdUniformlyOn
      (fun P : ProbeGoodPrime K S => probePrimeCorrection K a b c P.val)
      (probeEulerProduct K S a b c) probeEulerDomain := by
  have hball (T : Finset (ProbeGoodPrime K S)) (p : ProbeCoordinates)
      (hp : p ∈ probeEulerDomain) :
      (∑ P ∈ T, probePrimeLog K a b c P.val p) ∈
        Metric.closedBall (0 : ℂ) (probeEulerLogMajorant K S) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      _ ≤ ∑ P ∈ T, ‖probePrimeLog K a b c P.val p‖ := norm_sum_le _ _
      _ ≤ ∑ P ∈ T, 240 * probePrimeWeight K P.val :=
        Finset.sum_le_sum fun P _ => probePrimeLog_norm_le K a b c ha hb hc S hS P hp
      _ ≤ _ := (probeGoodPrime_majorant_summable K S).sum_le_tsum T
        (fun P _ => mul_nonneg (by norm_num) (probePrimeWeight_nonneg K P.val))
  have H := UniformContinuousOn.comp_tendstoUniformlyOn_eventually
    (Filter.Eventually.of_forall hball)
    (fun p hp => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact probeEulerLog_norm_le K S hS a b c ha hb hc hp)
    ((isCompact_closedBall (0 : ℂ) (probeEulerLogMajorant K S)).uniformContinuousOn_of_continuous
      Complex.continuous_exp.continuousOn)
    (probeEulerLog_tendstoUniformlyOn K S hS a b c ha hb hc)
  apply hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr
  apply H.congr (Filter.Eventually.of_forall ?_) |>.congr_right ?_
  · intro T p hp
    change Complex.exp (∑ P ∈ T, probePrimeLog K a b c P.val p) =
      ∏ P ∈ T, probePrimeCorrection K a b c P.val p
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun P _ => Complex.exp_log
      (probePrimeCorrection_ne_zero K a b c ha hb hc S hS P hp)
  · intro p hp
    exact (probeEulerProduct_eq_exp K S hS a b c ha hb hc hp).symm

theorem probeEulerLog_differentiableOn_path (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    {U : Set ℂ} (hU : IsOpen U) {x w z : ℂ → ℂ}
    (hx : DifferentiableOn ℂ x U) (hw : DifferentiableOn ℂ w U)
    (hz : DifferentiableOn ℂ z U)
    (hp : ∀ t ∈ U, probeEulerRegion (x t).re (w t).re (z t).re) :
    DifferentiableOn ℂ (fun t => probeEulerLog K S a b c (x t, w t, z t)) U := by
  apply Complex.differentiableOn_tsum_of_summable_norm (probeGoodPrime_majorant_summable K S)
  · intro P t ht
    exact (probePrimeLog_differentiableAt K a b c ha hb hc S hS P
      ((hx t ht).differentiableAt (hU.mem_nhds ht))
      ((hw t ht).differentiableAt (hU.mem_nhds ht))
      ((hz t ht).differentiableAt (hU.mem_nhds ht)) (hp t ht)).differentiableWithinAt
  · exact hU
  · intro P t ht
    exact probePrimeLog_norm_le K a b c ha hb hc S hS P (hp t ht)

theorem probeEulerProduct_differentiableOn_path (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    {U : Set ℂ} (hU : IsOpen U) {x w z : ℂ → ℂ}
    (hx : DifferentiableOn ℂ x U) (hw : DifferentiableOn ℂ w U)
    (hz : DifferentiableOn ℂ z U)
    (hp : ∀ t ∈ U, probeEulerRegion (x t).re (w t).re (z t).re) :
    DifferentiableOn ℂ (fun t => probeEulerProduct K S a b c (x t, w t, z t)) U :=
  (probeEulerLog_differentiableOn_path K S hS a b c ha hb hc hU hx hw hz hp).cexp.congr
    (fun t ht => probeEulerProduct_eq_exp K S hS a b c ha hb hc (hp t ht))

theorem probeEulerProduct_analyticOnNhd_path (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    {U : Set ℂ} (hU : IsOpen U) {x w z : ℂ → ℂ}
    (hx : DifferentiableOn ℂ x U) (hw : DifferentiableOn ℂ w U)
    (hz : DifferentiableOn ℂ z U)
    (hp : ∀ t ∈ U, probeEulerRegion (x t).re (w t).re (z t).re) :
    AnalyticOnNhd ℂ (fun t => probeEulerProduct K S a b c (x t, w t, z t)) U :=
  (probeEulerProduct_differentiableOn_path K S hS a b c ha hb hc hU hx hw hz hp).analyticOnNhd hU

theorem exists_probeEulerSmallTail_above (S₀ : Finset (ProbePrime K)) :
    ∃ S : Finset (ProbePrime K), S₀ ⊆ S ∧
      probePrimeCutoff K ⊆ S ∧ probeEulerLogMajorant K S ≤ 1 / 4 := by
  have H := (tendsto_tsum_compl_atTop_zero
    (fun P : ProbePrime K => 240 * probePrimeWeight K P)).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨S, hS⟩ := eventually_atTop.mp H
  refine ⟨S ∪ S₀ ∪ probePrimeCutoff K, ?_, Finset.subset_union_right, ?_⟩
  · exact Finset.subset_union_right.trans Finset.subset_union_left
  · exact (hS _ (Finset.subset_union_left.trans Finset.subset_union_left)).le

theorem exists_probeEulerSmallTail : ∃ S : Finset (ProbePrime K),
    probePrimeCutoff K ⊆ S ∧ probeEulerLogMajorant K S ≤ 1 / 4 := by
  obtain ⟨S, _, hS, hs⟩ := exists_probeEulerSmallTail_above K ∅
  exact ⟨S, hS, hs⟩

theorem probeEulerProduct_norm_sub_one_le (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (hsmall : probeEulerLogMajorant K S ≤ 1)
    (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    ‖probeEulerProduct K S a b c p - 1‖ ≤ 2 * probeEulerLogMajorant K S := by
  rw [probeEulerProduct_eq_exp K S hS a b c ha hb hc hp]
  exact (Complex.norm_exp_sub_one_le ((probeEulerLog_norm_le K S hS a b c ha hb hc hp).trans
    hsmall)).trans (mul_le_mul_of_nonneg_left
      (probeEulerLog_norm_le K S hS a b c ha hb hc hp) (by norm_num))

theorem exists_probeEulerProduct_uniform_half : ∃ S : Finset (ProbePrime K),
    probePrimeCutoff K ⊆ S ∧ ∀ (a b c : ProbePrime K → ℂ),
    (∀ P, ‖a P‖ ≤ 1) → (∀ P, ‖b P‖ ≤ 1) → (∀ P, ‖c P‖ ≤ 1) →
    ∀ p ∈ probeEulerDomain, ‖probeEulerProduct K S a b c p - 1‖ ≤ 1 / 2 := by
  obtain ⟨S, hS, hs⟩ := exists_probeEulerSmallTail K
  refine ⟨S, hS, fun a b c ha hb hc p hp => ?_⟩
  exact (probeEulerProduct_norm_sub_one_le K S hS (by linarith) a b c ha hb hc hp).trans
    (by linarith)

end
end ArtinMatthews
