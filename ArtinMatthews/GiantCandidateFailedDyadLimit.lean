module

public import ArtinMatthews.GiantCandidateCoinProxy
public import ArtinMatthews.GiantCandidateFailedBoxMean
public import ArtinMatthews.GiantCandidateFailedDyadBudget
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

/-! Uniform convergence of the literal full-dyad failure probabilities
passes to the original weighted tuple mass and its complex contribution. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Asymptotics
noncomputable section

def GiantCandidateUniformFailedBoxDecay (γ q threshold : ℝ) (j : ℕ) : Prop :=
  ∀ δ : ℝ,0 < δ → ∀ᶠ x : ℝ in atTop,∀ H : Fin j → ℕ,
    (∀ i,x^(γ/2) ≤ (H i:ℝ)) →
    giantCandidateFailedBoxMean x threshold (giantCandidateCoinScale q j) q H ≤ δ

theorem giantCandidateFailedProxyMass_nonneg_eventually {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (j : ℕ) (hj : 0 < j) (threshold T γ : ℝ) :
    ∀ᶠ x : ℝ in atTop,0 ≤ giantCandidateFailedProxyMass x threshold (giantCandidateCoinScale q j) q T γ j := by
  filter_upwards [giantCandidateCoinMass_actual_bounds hq0 hq1 j hj] with x hx
  unfold giantCandidateFailedProxyMass
  exact div_nonneg (sum_nonneg (fun t _ =>
    mul_nonneg (hx threshold (∏ i,t i)).2.1 (prod_nonneg (fun _ _ => norm_nonneg _)))) (Nat.cast_nonneg _)

theorem giant_candidate_failedProxyMass_isLittleO_of_dyad_mean {T γ q threshold : ℝ}
    (hT : 0 < T) (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) (hj : 0 < j)
    (hmean : GiantCandidateUniformFailedBoxDecay γ q threshold j) :
    (fun x : ℝ => giantCandidateFailedProxyMass x threshold (giantCandidateCoinScale q j) q T γ j)
      =o[atTop] (fun x : ℝ => x/Real.log x) := by
  obtain ⟨D,hD,hB⟩ := giantCandidateFailedProxyMass_bound_of_dyad_mean hT hγ hq0 hq1 j hj
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  filter_upwards [hB,hmean (ε/D) (div_pos hε hD),
    giantCandidateFailedProxyMass_nonneg_eventually hq0 hq1 j hj threshold T γ,
    eventually_gt_atTop (1:ℝ)] with x hb hm hn hx
  have hscale : 0 ≤ x/Real.log x := (div_pos (zero_lt_one.trans hx) (Real.log_pos hx)).le
  simp only [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_nonneg hscale]
  calc
    _ ≤ D*(ε/D)*(x/Real.log x) := hb threshold (ε/D) (div_pos hε hD).le hm
    _ = _ := by rw [mul_comm D (ε/D),div_mul_cancel₀ ε hD.ne']

theorem giant_candidate_failedProxy_isLittleO_of_dyad_mean {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ i,0 < e i ∧ e i < 1) {M : ℕ} (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {T γ q threshold : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (j : ℕ) (hj : 0 < j) (hmean : GiantCandidateUniformFailedBoxDecay γ q threshold j) :
    (fun x : ℝ => giantCandidateWeightedStrippedProxy e χ ε Φ T γ j x
      (giantCandidateFailedCoinMass x threshold (giantCandidateCoinScale q j) q j))
      =o[atTop] (fun x : ℝ => x/Real.log x) := by
  obtain ⟨D,_,hD⟩ := giantCandidateFailedProxyError_bound e he χ hε hεq Φ hΦ hT.le γ hq0 hq1 j hj
  have hO : (fun x : ℝ => giantCandidateWeightedStrippedProxy e χ ε Φ T γ j x
      (giantCandidateFailedCoinMass x threshold (giantCandidateCoinScale q j) q j))
      =O[atTop] (fun x : ℝ =>
        giantCandidateFailedProxyMass x threshold (giantCandidateCoinScale q j) q T γ j) := by
    apply Asymptotics.IsBigO.of_bound D
    filter_upwards [hD,giantCandidateFailedProxyMass_nonneg_eventually hq0 hq1 j hj threshold T γ]
      with x h hpos
    simpa only [Real.norm_eq_abs,abs_of_nonneg hpos] using h threshold
  exact hO.trans_isLittleO (giant_candidate_failedProxyMass_isLittleO_of_dyad_mean hT hγ hq0 hq1 j hj hmean)

end
end ArtinMatthews
