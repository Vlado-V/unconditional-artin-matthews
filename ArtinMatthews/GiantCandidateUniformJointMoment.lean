module

public import ArtinMatthews.GiantCandidateBoxBinomialMoment
public import ArtinMatthews.GiantCandidateActualJointMoment
public import ArtinMatthews.GiantCandidateModelMomentBound
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

/-! The relative comparison gives an absolute uniform error at every
fixed order. The exact falling-factorial normalization is retained. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter
open scoped BigOperators Topology

theorem giantCandidateBoxFallingFactorial_eq_binomial {ι : Type*} [Fintype ι] {j : ℕ}
    (S : Fin j → Finset ℕ) (G : ι → Finset ℕ)
    (side : ι → GiantCandidateHitSide) (k : ι → ℕ) :
    (∑ t∈Fintype.piFinset S,
      ∏ i,((giantCandidateHitSet (G i) (side i) (∏ v,t v)).card.descFactorial (k i):ℝ))/
        ((Fintype.piFinset S).card:ℝ) =
      (∏ i,((k i).factorial:ℝ))*giantCandidateBoxBinomialMoment S G side k := by
  unfold giantCandidateBoxBinomialMoment
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul,prod_mul_distrib]
  rw [← mul_sum,mul_div_assoc]

private theorem giantCandidateMomentRelative_abs_le {a b C ε : ℝ} (j : ℕ)
    (hb : 0≤b) (hC : b≤C) (hε : 0≤ε) (hε₁ : ε≤1)
    (hlo : (1-ε)^j*b≤a) (hhi : a≤(1+ε)^j*b) :
    |a-b| ≤ max (1-(1-ε)^j) ((1+ε)^j-1)*C := by
  have hl : 0≤1-(1-ε)^j :=
    sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hε₁) (by linarith only [hε]))
  have hm : 0 ≤ max (1-(1-ε)^j) ((1+ε)^j-1) := hl.trans (le_max_left _ _)
  have h₁ := mul_le_mul (le_max_left (1-(1-ε)^j) ((1+ε)^j-1)) hC hb hm
  have h₂ := mul_le_mul (le_max_right (1-(1-ε)^j) ((1+ε)^j-1)) hC hb hm
  exact abs_le.mpr ⟨by linarith only [hlo,h₁],by linarith only [hhi,h₂]⟩

private theorem giantCandidateMomentComparisonError_tendsto (C : ℝ) (j : ℕ) :
    Tendsto (fun x : ℝ => max (1-(1-(Real.log x)^(-(1:ℝ)))^j)
      ((1+(Real.log x)^(-(1:ℝ)))^j-1)*C) atTop (𝓝 0) := by
  let E (x : ℝ) := (Real.log x)^(-(1:ℝ))
  have hE : Tendsto E atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).comp Real.tendsto_log_atTop
  have hconst : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 (1:ℝ)) := tendsto_const_nhds
  have h₁ : Tendsto (fun x => 1-(1-E x)^j) atTop (𝓝 0) := by
    have h := hconst.sub ((hconst.sub hE).pow j)
    simpa only [sub_zero,one_pow,sub_self] using h
  have h₂ : Tendsto (fun x => (1+E x)^j-1) atTop (𝓝 0) := by
    have h := ((hconst.add hE).pow j).sub hconst
    simpa only [add_zero,one_pow,sub_self] using h
  simpa only [E,max_self,zero_mul] using (h₁.max h₂).mul_const C

theorem giant_candidate_actual_joint_binomial_moment_uniform
    {ι : Type*} [Fintype ι] (side : ι → GiantCandidateHitSide) (k : ι → ℕ)
    (τ : ℝ) (hτ : 0<τ) {j : ℕ} (hj : 0<j) {B : ℝ} (hB : 0≤B)
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ x : ℝ in atTop,∀ G : ι → Finset ℕ,(∀ i,G i ⊆ giantCandidateFullPrimes x) →
      Pairwise (fun i l => side i=side l → Disjoint (G i) (G l)) →
      (∀ i,(∑ p∈G i,1/(p:ℝ))≤B) →
      ∃ hG : ∀ i p,p∈G i → p.Prime,
        ∀ H : Fin j → ℕ,(∀ v,x^τ≤(H v:ℝ)) →
        let W := Real.exp ((Real.log x)^(6/25:ℝ))
        let S (v : Fin j) := giantCandidateRoughFullDyad W (H v)
        |giantCandidateBoxBinomialMoment S G side k-giantCandidateModelBinomialMoment j G side k hG|≤δ := by
  let C := ∏ i,((j:ℝ)*B)^(k i)/((k i).factorial:ℝ)
  have hlim := (giantCandidateMomentComparisonError_tendsto C j).eventually (Iio_mem_nhds hδ)
  filter_upwards [giant_candidate_actual_joint_binomial_moment_eventually side k τ 1 hτ zero_le_one j,
    hlim,Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)] with x hm hroom hL
  intro G hG hdis hmass
  obtain ⟨hG',hb⟩ := hm G hG
  refine ⟨hG',?_⟩
  intro H hH
  let ε := (Real.log x)^(-(1:ℝ))
  have hε : 0≤ε := Real.rpow_nonneg (zero_le_one.trans hL) _
  have hε₁ : ε≤1 := by
    simpa only [ε,Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : -(1:ℝ)≤0)
  have hC := giantCandidateModelBinomialMoment_le hj G side k hG' hdis hB hmass
  have hB₀ := giantCandidateModelBinomialMoment_nonneg j G side k hG'
  exact (giantCandidateMomentRelative_abs_le j hB₀ hC hε hε₁ (hb H hH).1 (hb H hH).2).trans hroom.le

end
end ArtinMatthews
