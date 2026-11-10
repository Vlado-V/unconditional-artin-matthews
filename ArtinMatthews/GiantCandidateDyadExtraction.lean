module

public import ArtinMatthews.GiantCandidateFailedDyadLimit
public import ArtinMatthews.GiantCandidateCoinExpansion
public import ArtinMatthews.GiantPrimeExtractionArithmetic
public import ArtinMatthews.GiantCandidateActualPrimeRemoval
public import ArtinMatthews.GiantCandidateCoinCorrelation
public import ArtinMatthews.GiantCandidateDyadBudget
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

/-! The original prime tuple reduces to the literal signed correlations
as soon as its actual full-dyad failed probabilities tend to zero. -/
namespace ArtinMatthews
open Filter
open scoped Asymptotics ContDiff
noncomputable section

theorem giant_candidate_strippedProxy_sub_signed_isLittleO_of_dyad_mean {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i,0 < e i ∧ e i < 1) {M : ℕ} (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {T γ q threshold : ℝ} (hT : 0 ≤ T) (hΦzero : Φ 0=0) (hhigh : ∀ t,T<t → Φ t=0)
    (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) (hj : 0 < j)
    (hmean : GiantCandidateUniformFailedBoxDecay γ q threshold j) :
    (fun x => giantOrdinaryStrippedProxyTupleSum giantCandidateFullPrimes e χ
      (giantMarkedCenteredCore ε) Φ (T+1) γ j x -
        giantCandidateSignedCorrelationSum e χ ε Φ T γ j x threshold (giantCandidateCoinScale q j) q)
      =o[atTop] (fun x : ℝ => x/Real.log x) := by
  let c := giantCandidateCoinScale q j
  let R (x : ℝ) := giantCandidateWeightedStrippedProxy e χ ε Φ (T+1) γ j x
    (giantCandidateRetainedCoinMass x threshold c q j)
  let F (x : ℝ) := giantCandidateWeightedStrippedProxy e χ ε Φ (T+1) γ j x
    (giantCandidateFailedCoinMass x threshold c q j)
  let S (x : ℝ) := giantCandidateSignedCorrelationSum e χ ε Φ T γ j x threshold c q
  have hT1 : 0 < T+1 := by positivity
  have hF : F =o[atTop] (fun x : ℝ => x/Real.log x) :=
    giant_candidate_failedProxy_isLittleO_of_dyad_mean e he χ hε hεq Φ hΦ hT1 hγ hq0 hq1 j hj hmean
  have hR : (fun x => R x-S x) =O[atTop] (fun x : ℝ => x*(Real.log x)^(-(1/10:ℝ))/Real.log x) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [giantCandidateRetainedProxy_signedCorrelation_log_saving e he χ hε hεq Φ hΦ
        hT hΦzero hhigh hγ hq0 hq1 j hj 2,
      eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
      with x h hx hL
    let L := Real.log x
    have hL0 : 0 < L := Real.log_pos hx
    have hx0 : 0 ≤ x := zero_le_one.trans hx.le
    have hnonneg : 0 ≤ x*L^(-(1/10:ℝ))/L := by positivity
    change ‖R x-S x‖ ≤ 1*‖x*L^(-(1/10:ℝ))/L‖
    rw [one_mul,Real.norm_eq_abs,abs_of_nonneg hnonneg]
    calc
      _ ≤ x*L^(-(2:ℝ)) := h threshold
      _ ≤ x*L^(-(1/10:ℝ)-1) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)) hx0
      _ = _ := by rw [Real.rpow_sub hL0,Real.rpow_one,mul_div_assoc]
  apply ((hR.trans_isLittleO giantCandidateLogTenth_isLittleO).add hF).congr' _ EventuallyEq.rfl
  filter_upwards [] with x
  change (R x-S x)+F x = _
  rw [giantCandidateStrippedProxy_partition e χ ε Φ (T+1) γ j x threshold c q]
  change (R x-S x)+F x = (R x+F x)-S x
  abel

theorem giant_ordinary_tuple_sub_signed_isLittleO_of_dyad_mean {J : Type}
    [Fintype J] [DecidableEq J] (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ i,(1/10:ℝ)<e i ∧ e i<(1/5:ℝ))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    (Φ : ℝ → ℝ) {a T : ℝ} (ha : 0 < a) (hT : 0 < T)
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hΦ : ContDiff ℝ ∞ Φ)
    {γ q threshold : ℝ} (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) (j : ℕ) (hj : 2 ≤ j)
    (hdepth : 100*(5*(29+2*(((j-1)*(j-1)+6:ℕ):ℝ))+36) < (Fintype.card J:ℝ))
    (hmean : GiantCandidateUniformFailedBoxDecay γ q threshold j) :
    (fun x => giantOrdinaryTupleSum e χ (giantMarkedCenteredCore ε) Φ (T+1) γ j x -
      giantCandidateSignedCorrelationSum e χ ε Φ T γ j x threshold (giantCandidateCoinScale q j) q)
      =o[atTop] (fun x : ℝ => x/Real.log x) := by
  have hT1 : 0 < T+1 := by positivity
  have hsupp1 : Function.support Φ ⊆ Set.Icc a (T+1) :=
    fun _ h => ⟨(hsupp h).1,(hsupp h).2.trans (by linarith)⟩
  have hΦzero : Φ 0 = 0 := by
    by_contra h
    exact (not_le_of_gt ha) (hsupp h).1
  have hhigh (t : ℝ) (ht : T<t) : Φ t=0 := by
    by_contra h
    exact (not_le_of_gt ht) (hsupp h).2
  have hslot := giant_ordinary_tuple_sub_actual_stripped_isLittleO e hinj he χ Φ ha hT1
    hsupp1 hΦ γ hγ hε hεq j hj hdepth
  have hproxy := giant_candidate_strippedProxy_sub_signed_isLittleO_of_dyad_mean e
    (fun i => ⟨(by norm_num : (0:ℝ)<1/10).trans (he i).1,(he i).2.trans (by norm_num)⟩)
    χ hε hεq Φ hΦ.continuous hT.le hΦzero hhigh hγ hq0 hq1 j (by omega) hmean
  apply (hslot.add hproxy).congr' _ EventuallyEq.rfl
  filter_upwards [] with x
  exact sub_add_sub_cancel _ _ _

end
end ArtinMatthews
