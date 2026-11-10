module

public import ArtinMatthews.GiantSamplingBilinearRows
public import ArtinMatthews.PrimeExtractionDyadicSupport
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

/-! The literal shifted bilinear sum on its finite support, partitioned
by the existing positive dyadic fibers. -/

noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators

namespace ArtinMatthews

def shiftedBilinearDyadicIndices (x : ℝ) : Finset ℕ :=
  Finset.range (Nat.log 2 ⌊2*x⌋₊ + 1)

def shiftedBilinearDyadicBlock (x : ℝ) (A : Finset ℕ) (k : ℕ) : Finset ℕ :=
  A ∩ primeExtractionDyadicBlock ⌊2*x⌋₊ k

@[simp] theorem mem_shiftedBilinearDyadicIndices {x : ℝ} {k : ℕ} :
    k ∈ shiftedBilinearDyadicIndices x ↔ k ≤ Nat.log 2 ⌊2*x⌋₊ := by
  simp [shiftedBilinearDyadicIndices]

theorem shiftedBilinearDyadicBlock_subset (x : ℝ) (A : Finset ℕ) (k : ℕ) :
    shiftedBilinearDyadicBlock x A k ⊆ A := Finset.inter_subset_left

theorem shiftedBilinearDyadicBlock_bounds {x : ℝ} {A : Finset ℕ} {k m : ℕ}
    (hm : m ∈ shiftedBilinearDyadicBlock x A k) : 2^k ≤ m ∧ m < 2*2^k :=
  primeExtractionDyadicBlock_bounds (Finset.mem_inter.mp hm).2

theorem shiftedBilinearDyadicBlock_card_le (x : ℝ) (A : Finset ℕ) (k : ℕ) :
    (shiftedBilinearDyadicBlock x A k).card ≤ 2^k :=
  (Finset.card_le_card Finset.inter_subset_right).trans (primeExtractionDyadicBlock_card_le ⌊2*x⌋₊ k)

theorem shiftedBilinearDyadicIndices_count_le {x : ℝ} (hx : 0 ≤ x) :
    ((shiftedBilinearDyadicIndices x).card : ℝ) ≤ 1+Real.log (2*x+1)/Real.log 2 := by
  unfold shiftedBilinearDyadicIndices
  rw [Finset.card_range]
  apply (primeExtractionDyadicIndex_count_le ⌊2*x⌋₊).trans
  have hcap : (⌊2*x⌋₊ : ℝ)+1 ≤ 2*x+1 := add_le_add (Nat.floor_le (by positivity)) le_rfl
  have hlog := Real.log_le_log (by positivity : 0 < (⌊2*x⌋₊ : ℝ)+1) hcap
  exact add_le_add le_rfl (div_le_div_of_nonneg_right hlog (Real.log_nonneg (by norm_num)))

private theorem shiftedBilinear_cutoff_mem {Φ : ℝ → ℝ} {x : ℝ} {m n : ℕ}
    (hx : 0 < x) (hsupp : Function.support Φ ⊆ Set.Icc 1 2)
    (hΦ : Φ (((m*n : ℕ) : ℝ)/x) ≠ 0) :
    m ∈ Finset.Ioc 0 ⌊2*x⌋₊ ∧ n ∈ Finset.Ioc 0 ⌊2*x⌋₊ := by
  have harg := hsupp hΦ
  have hlo : x ≤ ((m*n : ℕ) : ℝ) := by simpa only [one_mul] using (le_div_iff₀ hx).mp harg.1
  have hhi := Nat.le_floor ((div_le_iff₀ hx).mp harg.2)
  have hpos : 0 < m*n := Nat.cast_pos.mp (hx.trans_le hlo)
  have hm : 0 < m := Nat.pos_of_mul_pos_right hpos
  have hn : 0 < n := Nat.pos_of_mul_pos_left hpos
  exact ⟨Finset.mem_Ioc.mpr ⟨hm,(Nat.le_mul_of_pos_right m hn).trans hhi⟩,
    Finset.mem_Ioc.mpr ⟨hn,(Nat.le_mul_of_pos_left n hm).trans hhi⟩⟩

theorem giantCubicSamplingBilinear_eq_truncate (η : HeckeFamily.Character)
    (Φ : ℝ → ℝ) (x : ℝ) (A B : Finset ℕ) (α β : ℕ → ℂ)
    (hx : 0 < x) (hsupp : Function.support Φ ⊆ Set.Icc 1 2) :
    giantCubicSamplingBilinear η Φ x A B α β =
      giantCubicSamplingBilinear η Φ x (A ∩ Finset.Ioc 0 ⌊2*x⌋₊) (B ∩ Finset.Ioc 0 ⌊2*x⌋₊) α β := by
  let C := Finset.Ioc 0 ⌊2*x⌋₊
  let F (m n : ℕ) := α m * β n * (Φ (((m*n : ℕ) : ℝ)/x) : ℂ) * idealThetaCoeff η (m*n+1)
  have hzero (m n : ℕ) (hout : ¬ (m ∈ C ∧ n ∈ C)) : F m n = 0 := by
    have hΦ : Φ (((m*n : ℕ) : ℝ)/x) = 0 := by
      by_contra hne
      exact hout (shiftedBilinear_cutoff_mem hx hsupp hne)
    simp only [F,hΦ,Complex.ofReal_zero,mul_zero,zero_mul]
  change (∑ m ∈ A, ∑ n ∈ B, F m n) = ∑ m ∈ A ∩ C, ∑ n ∈ B ∩ C, F m n
  calc
    _ = ∑ m ∈ A ∩ C, ∑ n ∈ B, F m n := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro m hm hout
      apply Finset.sum_eq_zero
      intro n _
      exact hzero m n (fun h => hout (Finset.mem_inter.mpr ⟨hm,h.1⟩))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro n hn hout
      exact hzero m n (fun h => hout (Finset.mem_inter.mpr ⟨hn,h.2⟩))

private theorem shiftedBilinear_truncated_sum {R : Type*} [AddCommMonoid R]
    (x : ℝ) (A : Finset ℕ) (f : ℕ → R) :
    (∑ m ∈ A ∩ Finset.Ioc 0 ⌊2*x⌋₊, f m) =
      ∑ k ∈ shiftedBilinearDyadicIndices x, ∑ m ∈ shiftedBilinearDyadicBlock x A k, f m := by
  have hmap (m : ℕ) (hm : m ∈ A ∩ Finset.Ioc 0 ⌊2*x⌋₊) :
      Nat.log 2 m ∈ shiftedBilinearDyadicIndices x :=
    mem_shiftedBilinearDyadicIndices.mpr (Nat.log_mono_right (Finset.mem_Ioc.mp (Finset.mem_inter.mp hm).2).2)
  have hfiber (k : ℕ) : ((A ∩ Finset.Ioc 0 ⌊2*x⌋₊).filter (fun m => Nat.log 2 m = k)) =
      shiftedBilinearDyadicBlock x A k := by
    ext m
    simp only [shiftedBilinearDyadicBlock, primeExtractionDyadicBlock, Finset.mem_inter,
      Finset.mem_filter, and_assoc]
  simp_rw [← hfiber]
  exact (Finset.sum_fiberwise_of_maps_to hmap f).symm

theorem giantCubicSamplingBilinear_eq_dyadic (η : HeckeFamily.Character)
    (Φ : ℝ → ℝ) (x : ℝ) (A B : Finset ℕ) (α β : ℕ → ℂ)
    (hx : 0 < x) (hsupp : Function.support Φ ⊆ Set.Icc 1 2) :
    giantCubicSamplingBilinear η Φ x A B α β =
      ∑ k ∈ shiftedBilinearDyadicIndices x, ∑ l ∈ shiftedBilinearDyadicIndices x,
        giantCubicSamplingBilinear η Φ x (shiftedBilinearDyadicBlock x A k)
          (shiftedBilinearDyadicBlock x B l) α β := by
  rw [giantCubicSamplingBilinear_eq_truncate η Φ x A B α β hx hsupp]
  let C := Finset.Ioc 0 ⌊2*x⌋₊
  let D := shiftedBilinearDyadicIndices x
  let F (m n : ℕ) := α m * β n * (Φ (((m*n : ℕ) : ℝ)/x) : ℂ) * idealThetaCoeff η (m*n+1)
  change (∑ m ∈ A ∩ C, ∑ n ∈ B ∩ C, F m n) =
    ∑ k ∈ D, ∑ l ∈ D, ∑ m ∈ shiftedBilinearDyadicBlock x A k,
      ∑ n ∈ shiftedBilinearDyadicBlock x B l, F m n
  calc
    _ = ∑ k ∈ D, ∑ m ∈ shiftedBilinearDyadicBlock x A k, ∑ n ∈ B ∩ C, F m n :=
      shiftedBilinear_truncated_sum x A _
    _ = ∑ k ∈ D, ∑ m ∈ shiftedBilinearDyadicBlock x A k, ∑ l ∈ D,
        ∑ n ∈ shiftedBilinearDyadicBlock x B l, F m n := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro m _
      exact shiftedBilinear_truncated_sum x B _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

theorem shiftedBilinearDyadicBlock_active_bounds {Φ : ℝ → ℝ} {x lo hi : ℝ}
    {A B : Finset ℕ} {k l m n : ℕ} (hx : 0 < x) (hsupp : Function.support Φ ⊆ Set.Icc 1 2)
    (hrow : ∀ m ∈ A, lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi)
    (hm : m ∈ shiftedBilinearDyadicBlock x A k) (hn : n ∈ shiftedBilinearDyadicBlock x B l)
    (hΦ : Φ (((m*n : ℕ) : ℝ)/x) ≠ 0) :
    ((2^k : ℕ) : ℝ)*((2^l : ℕ) : ℝ) ≤ 2*x ∧
      x ≤ 4*(((2^k : ℕ) : ℝ)*((2^l : ℕ) : ℝ)) ∧ ((2^k : ℕ) : ℝ) ≤ hi ∧ lo ≤ 2*((2^k : ℕ) : ℝ) := by
  have hsuppC : Function.support (fun t : ℝ => (Φ t : ℂ)) ⊆ Set.Icc 1 2 := by
    intro y hy
    exact hsupp (Complex.ofReal_ne_zero.mp hy)
  obtain ⟨hprod, hxprod⟩ := primeExtractionDyadicCutoff_height hx hsuppC
    (Finset.mem_inter.mp hm).2 (Finset.mem_inter.mp hn).2 (Complex.ofReal_ne_zero.mpr hΦ)
  obtain ⟨hlo, hhi⟩ := hrow m (shiftedBilinearDyadicBlock_subset x A k hm)
  have hb := shiftedBilinearDyadicBlock_bounds hm
  have hmlo : ((2^k : ℕ) : ℝ) ≤ m := by exact_mod_cast hb.1
  have hmhi : (m : ℝ) ≤ 2*((2^k : ℕ) : ℝ) := by exact_mod_cast hb.2.le
  exact ⟨by simpa only [primeExtractionDyadicHeight, Nat.cast_mul] using hprod,
    by simpa only [primeExtractionDyadicHeight, Nat.cast_mul, one_mul] using hxprod,
    hmlo.trans hhi, hlo.trans hmhi⟩

theorem giantCubicSamplingBilinear_eq_zero_of_no_active (η : HeckeFamily.Character)
    (Φ : ℝ → ℝ) (x : ℝ) (A B : Finset ℕ) (α β : ℕ → ℂ)
    (hzero : ¬ ∃ m ∈ A, ∃ n ∈ B, Φ (((m*n : ℕ) : ℝ)/x) ≠ 0) :
    giantCubicSamplingBilinear η Φ x A B α β = 0 := by
  unfold giantCubicSamplingBilinear
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  have hΦ : Φ (((m*n : ℕ) : ℝ)/x) = 0 := by
    by_contra hne
    exact hzero ⟨m,hm,n,hn,hne⟩
  simp only [hΦ,Complex.ofReal_zero,mul_zero,zero_mul]

end ArtinMatthews
