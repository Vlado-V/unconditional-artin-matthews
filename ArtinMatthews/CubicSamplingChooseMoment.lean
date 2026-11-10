module

public import ArtinMatthews.DivisorWeights
public import Mathlib.Order.Interval.Finset.Nat
public import ArtinMatthews.MarkedProgressionExpansion
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The binomial moment of actual marking-prime hits follows from the
squarefree product divisor and the true positive interval of multiples. -/

noncomputable section
namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

theorem cubicSampling_positive_multiples_le (N d : ℕ) :
    (∑ u ∈ Finset.Icc 1 N, if d ∣ u then (1 : ℝ) else 0) ≤ (N : ℝ) / d := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  by_cases hd : d = 0
  · subst d
    have hzero : (Finset.Icc 1 N).filter (fun u => 0 ∣ u) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨hU, hdu⟩ := Finset.mem_filter.mp hu
      have hpos := (Finset.mem_Icc.mp hU).1
      rw [zero_dvd_iff.mp hdu] at hpos
      omega
    rw [hzero, Finset.card_empty, Nat.cast_zero, div_zero]
  · have hcard : ((Finset.Icc 1 N).filter (fun u => d ∣ u)).card ≤
        (Finset.Icc 1 (N / d)).card := by
      apply Finset.card_le_card_of_injOn (fun u => u / d)
      · intro u hu
        obtain ⟨hU, hdu⟩ := Finset.mem_filter.mp hu
        have hcancel := Nat.div_mul_cancel hdu
        have hpos : 1 ≤ u / d := by
          apply Nat.one_le_iff_ne_zero.mpr
          intro hz
          rw [hz, zero_mul] at hcancel
          exact (Nat.ne_of_gt (Finset.mem_Icc.mp hU).1) hcancel.symm
        exact Finset.mem_Icc.mpr ⟨hpos, Nat.div_le_div_right (Finset.mem_Icc.mp hU).2⟩
      · intro u hu v hv he
        exact (Nat.div_mul_cancel (Finset.mem_filter.mp hu).2).symm.trans
          ((congrArg (fun n : ℕ => n * d) he).trans
            (Nat.div_mul_cancel (Finset.mem_filter.mp hv).2))
    calc
      _ ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast (by simpa using hcard : _ ≤ N / d)
      _ ≤ _ := Nat.cast_div_le

theorem cubicSampling_binomial_hit_moment (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (N k : ℕ) {V : ℝ} (hV : 0 ≤ V) (hmass : ∑ p ∈ P, 1 / (p : ℝ) ≤ V) :
    (∑ u ∈ Finset.Icc 1 N, ((bandCount P u).choose k : ℝ)) ≤
      (N : ℝ) * (V ^ k / (k.factorial : ℝ)) := by
  have hrow (u : ℕ) : ((bandCount P u).choose k : ℝ) =
      ∑ T ∈ P.powersetCard k, if (∏ p ∈ T, p) ∣ u then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    have hfilter : (P.powersetCard k).filter (fun T => (∏ p ∈ T, p) ∣ u) =
        (activeDivisors P u).powersetCard k := by
      ext T
      constructor
      · intro hT
        obtain ⟨ht, hd⟩ := Finset.mem_filter.mp hT
        obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.mp ht
        have hall := (marked_prime_product_dvd_iff T (fun p hp => hP p (hsub hp)) u).mp hd
        exact Finset.mem_powersetCard.mpr ⟨fun p hp =>
          Finset.mem_filter.mpr ⟨hsub hp, hall p hp⟩, hc⟩
      · intro hT
        obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.mp hT
        have hs : T ⊆ P := fun p hp => (Finset.mem_filter.mp (hsub hp)).1
        exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hs, hc⟩,
          (marked_prime_product_dvd_iff T (fun p hp => hP p (hs hp)) u).mpr
            (fun p hp => (Finset.mem_filter.mp (hsub hp)).2)⟩
    rw [hfilter]
    simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_one, bandCount]
  simp_rw [hrow]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ T ∈ P.powersetCard k, (N : ℝ) / (∏ p ∈ T, p : ℕ) :=
      Finset.sum_le_sum (fun T _ => cubicSampling_positive_multiples_le N (∏ p ∈ T, p))
    _ = (N : ℝ) * BonferroniDensity.elementarySum P (fun p => 1 / (p : ℝ)) k := by
      rw [BonferroniDensity.elementarySum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _hT
      simp only [Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_const_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (BonferroniDensity.elementarySum_le_pow_div_factorial P (fun p => 1 / (p : ℝ))
        (fun p _ => by positivity) hV hmass k) (Nat.cast_nonneg _)

end ArtinMatthews
