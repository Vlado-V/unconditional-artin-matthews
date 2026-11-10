module

public import ArtinMatthews.GiantCandidateFailedBoxMean
public import ArtinMatthews.GiantCandidateCoinProxy
public import ArtinMatthews.GiantProxyDyadKeyBounds
public import ArtinMatthews.GiantCandidateSlotError
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

/-! The original product-capped failure mass is bounded by full rough
dyad averages on the actual contributing keys. A missing strip
threshold or roughness condition gives exactly zero weight. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem giantCandidateFailedProxyMass_le_dyad_means (x threshold c q T γ : ℝ) (j : ℕ)
    (hz : 1 < x^γ) (hhalf : x^(γ/2) ≤ x^γ/2)
    (hfail : ∀ v : ℕ,0 ≤ giantCandidateFailedCoinMass x threshold c q j v) :
    let N := ⌊T*x⌋₊
    let W := Real.exp ((Real.log x)^(6/25:ℝ))
    let A := giantCandidateSlotBound W (x^γ)
    let H (key : Fin j → ℕ) (i : Fin j) := (2:ℕ)^key i
    let K := (giantProxyDyadKeys j N).filter (fun key => ∀ i,x^(γ/2) ≤ (H key i:ℝ))
    giantCandidateFailedProxyMass x threshold c q T γ j ≤
      (A^j*(∑ key ∈ K, giantCandidateFailedBoxMean x threshold c q (H key) *
        ((giantCandidateFullRoughBox x (H key)).card:ℝ)))/(j.factorial:ℝ) := by
  classical
  let N := ⌊T*x⌋₊
  let W := Real.exp ((Real.log x)^(6/25:ℝ))
  let z := x^γ
  let A := giantCandidateSlotBound W z
  let H (key : Fin j → ℕ) (i : Fin j) := (2:ℕ)^key i
  let K := (giantProxyDyadKeys j N).filter (fun key => ∀ i,x^(γ/2) ≤ (H key i:ℝ))
  let C := giantCandidateFullPrimes x
  let r := giantCandidateFailedCoinMass x threshold c q j
  let a := giantCandidateStrippedSlotCoefficient C W z
  let F (t : Fin j → ℕ) := r (∏ i,t i)*(∏ i,‖a (t i)‖)
  let S₀ := giantOrderedProductTuples j N
  let S := S₀.filter (fun t => ∀ i,GiantCandidateProxySupport W z (t i))
  have hSsum : (∑ t ∈ S₀,F t) = ∑ t ∈ S,F t := by
    symm
    have hsub : S ⊆ S₀ := filter_subset _ _
    apply sum_subset hsub
    intro t ht hn
    have hnot : ¬∀ i,GiantCandidateProxySupport W z (t i) :=
      fun h => hn (mem_filter.mpr ⟨ht,h⟩)
    obtain ⟨i,hi⟩ := not_forall.mp hnot
    have ha : a (t i) = 0 := giantCandidateStrippedSlotCoefficient_eq_zero_of_not_support C W z (t i) hi
    have hp : (∏ i,‖a (t i)‖) = 0 :=
      Finset.prod_eq_zero (mem_univ i) (by rw [ha,norm_zero])
    dsimp only [F]
    rw [hp,mul_zero]
  have hmaps : ∀ t ∈ S,giantProxyDyadKey t ∈ K := by
    intro t ht
    obtain ⟨ht₀,hsup⟩ := mem_filter.mp ht
    obtain ⟨hpos,hN⟩ := mem_giantOrderedProductTuples.mp ht₀
    refine mem_filter.mpr ⟨giantProxyDyadKey_mem t hpos hN,?_⟩
    intro i
    have hhi := (giantProxyDyadKey_lower_upper t i (hpos i)).2
    rw [pow_succ,Nat.mul_comm] at hhi
    have hi : (t i:ℝ) < 2*(H (giantProxyDyadKey t) i:ℝ) := by exact_mod_cast hhi
    have hzi : z < (t i:ℝ) := (hsup i).1
    linarith only [hhalf,hi,hzi]
  have hsub (key : Fin j → ℕ) :
      S.filter (fun t => giantProxyDyadKey t=key) ⊆ giantCandidateFullRoughBox x (H key) := by
    intro t ht
    obtain ⟨htS,hkey⟩ := mem_filter.mp ht
    obtain ⟨ht₀,hsup⟩ := mem_filter.mp htS
    have hpos := (mem_giantOrderedProductTuples.mp ht₀).1
    apply Fintype.mem_piFinset.mpr
    intro i
    obtain ⟨hlo,hhi⟩ := giantProxyDyadKey_lower_upper t i (hpos i)
    rw [congrFun hkey i] at hlo hhi
    rw [pow_succ,Nat.mul_comm] at hhi
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hlo,hhi⟩,(hsup i).2⟩
  have hA : 0 ≤ A := giantCandidateSlotBound_nonneg hz
  have ha (m : ℕ) : ‖a m‖ ≤ A := by
    apply (giantCandidateStrippedSlotCoefficient_norm_le_envelope C hz m).trans
    unfold giantCandidateProxyEnvelope
    split_ifs
    · exact le_rfl
    · exact hA
  have hF (t : Fin j → ℕ) : F t ≤ A^j*r (∏ i,t i) := by
    have hp : (∏ i,‖a (t i)‖) ≤ A^j := by
      simpa only [prod_const,card_univ,Fintype.card_fin] using
        (prod_le_prod₀ (s:=(univ : Finset (Fin j))) (fun _ _ => norm_nonneg _)
          (fun i _ => ha (t i)))
    exact (mul_le_mul_of_nonneg_left hp (hfail (∏ i,t i))).trans_eq (mul_comm _ _)
  change (∑ t ∈ S₀,F t)/(j.factorial:ℝ) ≤
    (A^j*(∑ key ∈ K,giantCandidateFailedBoxMean x threshold c q (H key)*
      ((giantCandidateFullRoughBox x (H key)).card:ℝ)))/(j.factorial:ℝ)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [hSsum,← sum_fiberwise_of_maps_to hmaps F,Finset.mul_sum]
  apply sum_le_sum
  intro key _
  rw [giantCandidateFailedBoxMean_mul_card,Finset.mul_sum]
  exact (sum_le_sum (fun t _ => hF t)).trans
    (sum_le_sum_of_subset_of_nonneg (hsub key) (fun t _ _ => mul_nonneg (pow_nonneg hA j) (hfail (∏ i,t i))))

end
end ArtinMatthews
