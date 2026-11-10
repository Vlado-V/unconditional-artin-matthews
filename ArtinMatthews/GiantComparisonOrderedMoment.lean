module

public import ArtinMatthews.GiantComparisonEndpointGlobalMoment
public import ArtinMatthews.GiantComparisonFreeMarking
public import ArtinMatthews.GiantCandidateSelectedGroups
public import ArtinMatthews.GiantComparisonNumberedMarks
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.UniformSpace.Uniformizable
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The actual fourth moments apply to the full ordered free-list
weight, using a fixed compact cutoff equal to one on the row ranges. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section

private theorem comparisonMomentCutoff_exists (R : ℝ) (hR : 1 ≤ R) :
    ∃ ψ : ℝ → ℂ, Continuous ψ ∧ HasCompactSupport ψ ∧ ∀ y ∈ Set.Icc 0 R, ψ y = 1 := by
  let ρ : ContDiffBump (0:ℝ) := ⟨R,R+1,zero_lt_one.trans_le hR,by linarith⟩
  let ψ (y : ℝ) : ℂ := (ρ y:ℝ)
  refine ⟨ψ,Complex.continuous_ofReal.comp ρ.continuous,?_,?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:ℝ) ρ.rOut)
    intro y hy
    apply Metric.ball_subset_closedBall
    rw [← ρ.support_eq]
    exact Complex.ofReal_ne_zero.mp hy
  · intro y hy
    have hball : y ∈ Metric.closedBall (0:ℝ) ρ.rIn := by
      rw [Metric.mem_closedBall,Real.dist_eq,sub_zero,abs_of_nonneg hy.1]
      exact hy.2
    change (ρ y:ℂ) = 1
    rw [ρ.one_of_mem_closedBall hball,Complex.ofReal_one]

theorem giantCandidateComparisonOrderedFourth_eventually {I : Type*} [Fintype I]
    (e : I → ℝ) (he : ∀ i, 0 < e i ∧ e i < 1)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) {m : ℕ} (χ : DirichletCharacter ℂ m)
    {γ R : ℝ} (hγ : 0 < γ) (hR : 1 ≤ R) (j : ℕ) (hj : 0 < j) (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : Finset (GiantCandidateGroupIndex x)) (C : S → Finset (Fin k))
        (Y : ℝ), 1 ≤ Y → Y ≤ x^2 →
      ∀ (q : ℝ), 0 ≤ q ∧ q ≤ 1 →
      ∀ (ZL ZR : Finset ℕ), ZL ⊆ Ioc 0 ⌊R*Y⌋₊ → ZR ⊆ Ioc 0 ⌊R*Y⌋₊ →
      let P (g : S) := giantCandidateGroup x g.val
      let W := giantComparisonOrderedFreeWeight P C 1 q
      let F := giantCandidateFirstEndpoint e ε x
      let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
        (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
      (∑ n ∈ ZL, ‖F n*(W n:ℂ)‖^4) ≤ B*Y*(Real.log x)^D ∧
      (∑ n ∈ ZR, ‖(χ n*G n)*(W n:ℂ)‖^4) ≤ B*Y*(Real.log x)^D := by
  obtain ⟨ψ,hψ,hcomp,hone⟩ := comparisonMomentCutoff_exists R hR
  obtain ⟨B,hB,D,hD,hbound⟩ := giantCandidateComparisonEndpointPower_eventually
    e he hε hεq χ hγ (A:=2) (by norm_num) hR j hj k 2 ψ ψ hψ hcomp hψ hcomp
  refine ⟨B,hB,D,hD,?_⟩
  filter_upwards [hbound,giantCandidateSelectedGroups_geometry_eventually] with x hx hg
  intro S C Y hY hYX q hq ZL ZR hZL hZR
  let P (g : S) := giantCandidateGroup x g.val
  let t (g : S) := 1+(C g).card
  let b : ((g : S) → Fin (t g) → ℕ) → ℂ := fun _ => 1
  let W := giantComparisonOrderedFreeWeight P C 1 q
  let F := giantCandidateFirstEndpoint e ε x
  let G := giantCandidateAllocationCore (giantCandidateFullPrimes x) (univ.biUnion P)
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j
  have ht (g : S) : t g ≤ k+1 := by
    have hc : (C g).card ≤ k := by
      simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ (C g))
    dsimp only [t]
    omega
  have hb : ∀ l ∈ sourceComparisonMarkChoices P t, ‖b l‖ ≤ 1 := by simp [b]
  have hYX' : Y ≤ x^(2:ℝ) := by rw [Real.rpow_two]; exact hYX
  have hm := hx S Y hY hYX' t (fun _ => q) ht (fun _ => hq) b b hb hb 0 ZL ZR hZL hZR
  have hw (n : ℕ) : sourceComparisonMarkWeight P t (fun _ => q) b n = (W n:ℂ) := by
    rw [sourceComparisonMarkWeight_eq_freeMarking_sum P (hg S).1 C 1 q b n]
    simp only [W,giantComparisonOrderedFreeWeight,b,sum_const,card_univ,nsmul_eq_mul,mul_one,Complex.ofReal_mul,Complex.ofReal_natCast]
    ring
  have hp (n : ℕ) (hn : n ∈ Ioc 0 ⌊R*Y⌋₊) : ψ ((n:ℝ)/Y) = 1 := by
    have hY0 : 0 < Y := zero_lt_one.trans_le hY
    have hnR : (n:ℝ) ≤ R*Y := (Nat.le_floor_iff (by positivity)).mp (mem_Ioc.mp hn).2
    exact hone _ ⟨div_nonneg (Nat.cast_nonneg _) hY0.le,(div_le_iff₀ hY0).mpr hnR⟩
  have hL (n : ℕ) (hn : n ∈ ZL) :
      giantCandidateComparisonLeftEndpoint e ε x Y 0 ψ P t (fun _ => q) b n = F n*(W n:ℂ) := by
    simp only [giantCandidateComparisonLeftEndpoint,giantComparisonWeightedEndpoint,
      hp n (hZL hn),hw,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,one_mul,F]
  have hR' (n : ℕ) (hn : n ∈ ZR) :
      giantCandidateComparisonRightEndpoint χ γ j x Y ψ P t (fun _ => q) b n =
        (χ n*G n)*(W n:ℂ) := by
    simp only [giantCandidateComparisonRightEndpoint,giantComparisonWeightedEndpoint,
      hp n (hZR hn),hw,one_mul,G]
  have hsumL : (∑ n ∈ ZL, ‖giantCandidateComparisonLeftEndpoint e ε x Y 0 ψ P t (fun _ => q) b n‖^(2^2:ℕ)) =
      ∑ n ∈ ZL, ‖F n*(W n:ℂ)‖^4 := by
    apply sum_congr rfl
    intro n hn
    rw [hL n hn]
    norm_num
  have hsumR : (∑ n ∈ ZR, ‖giantCandidateComparisonRightEndpoint χ γ j x Y ψ P t (fun _ => q) b n‖^(2^2:ℕ)) =
      ∑ n ∈ ZR, ‖(χ n*G n)*(W n:ℂ)‖^4 := by
    apply sum_congr rfl
    intro n hn
    rw [hR' n hn]
    norm_num
  rw [hsumL,hsumR] at hm
  exact hm

end
end ArtinMatthews
