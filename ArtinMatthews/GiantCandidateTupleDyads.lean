module

public import ArtinMatthews.GiantCandidateTupleError
public import ArtinMatthews.GiantProxyDyadKeyBounds
public import ArtinMatthews.PrimeExtractionDyadicPartition
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

/-! Positive error mass is estimated over full coordinate dyads, while
the allowed dyad keys come from the original product cutoff. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giantCandidatePositiveTupleMass_le_dyad_products {j : ℕ} (N : ℕ)
    (i : Fin j) (d u : ℕ → ℝ) (hd : ∀ m,0 ≤ d m) (hu : ∀ m,0 ≤ u m) :
    giantCandidatePositiveTupleMass N i d u ≤
      ∑ key ∈ giantProxyDyadKeys j N,
        ∏ v,∑ m ∈ primeExtractionDyadicBlock N (key v),if v=i then d m else u m := by
  classical
  let S := giantOrderedProductTuples j N
  let K := giantProxyDyadKeys j N
  let F (v : Fin j) (m : ℕ) := if v=i then d m else u m
  let G (t : Fin j → ℕ) := ∏ v,F v (t v)
  have hmaps : ∀ t∈S,giantProxyDyadKey t∈K := by
    intro t ht
    obtain ⟨ht₀,htN⟩ := mem_giantOrderedProductTuples.mp ht
    exact giantProxyDyadKey_mem t ht₀ htN
  change (∑ t ∈ S,G t) ≤ ∑ key ∈ K,∏ v,∑ m ∈ primeExtractionDyadicBlock N (key v),F v m
  rw [← sum_fiberwise_of_maps_to hmaps G]
  apply sum_le_sum
  intro key _
  let T := Fintype.piFinset (fun v => primeExtractionDyadicBlock N (key v))
  have hsub : S.filter (fun t => giantProxyDyadKey t=key) ⊆ T := by
    intro t ht
    obtain ⟨hs,hkey⟩ := mem_filter.mp ht
    obtain ⟨ht₀,htN⟩ := mem_giantOrderedProductTuples.mp hs
    apply Fintype.mem_piFinset.mpr
    intro v
    have hdvd : t v ∣ ∏ w,t w := dvd_prod_of_mem t (mem_univ v)
    have htv := (Nat.le_of_dvd (prod_pos (fun w _ => ht₀ w)) hdvd).trans htN
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨ht₀ v,htv⟩,congrFun hkey v⟩
  rw [prod_univ_sum]
  exact sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => prod_nonneg (fun v _ => by
    unfold F
    split_ifs
    · exact hd _
    · exact hu _))

theorem giantCandidatePositiveTupleMass_le_rows {j : ℕ} (hj : 2 ≤ j)
    (N : ℕ) (hN : 0 < N) (i : Fin j) (d u : ℕ → ℝ)
    (hd : ∀ m,0 ≤ d m) (hu : ∀ m,0 ≤ u m)
    (U D E : ℝ) (hU : 0 ≤ U) (hD : 0 ≤ D) (hE : 0 ≤ E) (I : Finset ℕ)
    (hrowU : ∀ k,(∑ m ∈ primeExtractionDyadicBlock N k,u m) ≤ U*(2:ℝ)^k)
    (hrowD : ∀ k,(∑ m ∈ primeExtractionDyadicBlock N k,d m) ≤
      (D+(if k∈I then E else 0))*(2:ℝ)^k) :
    let K := ((Nat.log 2 N+1:ℕ):ℝ)
    giantCandidatePositiveTupleMass N i d u ≤
      2*(N:ℝ)*U^(j-1)*(D*K^(j-1)+E*(I.card:ℝ)*K^(j-2)) := by
  classical
  let K := ((Nat.log 2 N+1:ℕ):ℝ)
  let S := giantProxyDyadKeys j N
  let T := S.filter (fun key => key i∈I)
  let F (v : Fin j) (m : ℕ) := if v=i then d m else u m
  let A (key : Fin j → ℕ) : ℝ := D+(if key i∈I then E else 0)
  let B (key : Fin j → ℕ) (v : Fin j) : ℝ := if v=i then A key else U
  have hbox (key : Fin j → ℕ) :
      (∏ v,∑ m ∈ primeExtractionDyadicBlock N (key v),F v m) ≤
        A key*U^(j-1)*giantProxyDyadKeyWeight key := by
    have hfactor (v : Fin j) :
        (∑ m ∈ primeExtractionDyadicBlock N (key v),F v m) ≤ B key v*(2:ℝ)^key v := by
      by_cases hvi : v=i
      · subst v
        simpa only [F,B,A,ite_eq_left rfl] using hrowD (key i)
      · simpa only [F,B,ite_eq_right hvi] using hrowU (key v)
    calc
      _ ≤ ∏ v,B key v*(2:ℝ)^key v := by
        apply prod_le_prod₀
        · intro v _
          apply sum_nonneg
          intro m _
          unfold F
          split_ifs
          · exact hd _
          · exact hu _
        · exact fun v _ => hfactor v
      _ = _ := by
        rw [prod_mul_distrib,← giantProxyDyadKeyWeight_eq_prod,
          ← mul_prod_erase univ (B key) (mem_univ i)]
        have hrest : (∏ v ∈ univ.erase i,B key v) = U^(j-1) := by
          calc
            _ = ∏ _v ∈ (univ : Finset (Fin j)).erase i,U :=
              prod_congr rfl (fun v hv => ite_eq_right (mem_erase.mp hv).1)
            _ = _ := by rw [prod_const,card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin]
        rw [hrest,show B key i=A key from ite_eq_left rfl]
  have hsplit :
      (∑ key ∈ S,A key*U^(j-1)*giantProxyDyadKeyWeight key) =
        U^(j-1)*(D*(∑ key ∈ S,giantProxyDyadKeyWeight key)+E*(∑ key ∈ T,giantProxyDyadKeyWeight key)) := by
    calc
      _ = U^(j-1)*(∑ key ∈ S,(D*giantProxyDyadKeyWeight key+
          (if key i∈I then E*giantProxyDyadKeyWeight key else 0))) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro key _
        unfold A
        split_ifs <;> ring
      _ = _ := by rw [sum_add_distrib,← mul_sum,← sum_filter,← mul_sum]
  change _ ≤ 2*(N:ℝ)*U^(j-1)*(D*K^(j-1)+E*(I.card:ℝ)*K^(j-2))
  calc
    _ ≤ ∑ key ∈ S,∏ v,∑ m ∈ primeExtractionDyadicBlock N (key v),F v m :=
      giantCandidatePositiveTupleMass_le_dyad_products N i d u hd hu
    _ ≤ ∑ key ∈ S,A key*U^(j-1)*giantProxyDyadKeyWeight key :=
      sum_le_sum (fun key _ => hbox key)
    _ = _ := hsplit
    _ ≤ U^(j-1)*(D*(2*(N:ℝ)*K^(j-1))+E*(2*(N:ℝ)*(I.card:ℝ)*K^(j-2))) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (giantProxyDyadKeys_weight_sum_le j N (by omega) hN) hD)
          (mul_le_mul_of_nonneg_left (giantProxyDyadKeys_restricted_weight_sum_le j N hj hN i I) hE))
        (pow_nonneg hU _)
    _ = _ := by ring

end
end ArtinMatthews
