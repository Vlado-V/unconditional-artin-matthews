module

public import ArtinMatthews.GiantCandidateSlotError
public import ArtinMatthews.PrimeExtractionDyadicPartition
public import ArtinMatthews.MarkedMajorArcRoughLow
public import ArtinMatthews.PrimeExtractionRelevantGeometry
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

/-! Positive rough counts on the original finite dyadic blocks. The
positive-power support is needed only if the block contributes. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter
open scoped BigOperators

def giantCandidateRoughDyad (W z : ℝ) (N k : ℕ) : Finset ℕ :=
  (primeExtractionDyadicBlock N k).filter (GiantCandidateProxySupport W z)

theorem giantCandidateRoughDyad_subset_prefix (W z : ℝ) (N k : ℕ) :
    giantCandidateRoughDyad W z N k ⊆
      (Ioc 0 (2*2^k)).filter (fun m => ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p ∣ m) := by
  intro m hm
  obtain ⟨hb,hs⟩ := mem_filter.mp hm
  exact mem_filter.mpr ⟨mem_Ioc.mpr
    ⟨(mem_Ioc.mp (mem_filter.mp hb).1).1,(primeExtractionDyadicBlock_bounds hb).2.le⟩,hs.2⟩

theorem giant_candidate_rough_prefix_card_eventually (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop, ∀ M : ℕ, Real.exp (τ*L) ≤ (M:ℝ) →
      let W := Real.exp (L^(6/25:ℝ))
      (((Ioc 0 M).filter (fun m => ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p ∣ m)).card:ℝ) ≤
        2*(M:ℝ)*markedSieveEulerProduct W := by
  classical
  filter_upwards [marked_major_rough_prefix_low 0 τ 0 1 (by norm_num) hτ
    (by norm_num) (by norm_num)] with L hcount
  intro M hM
  let W := Real.exp (L^(6/25:ℝ))
  let V := markedSieveEulerProduct W
  let B := (Ioc 0 M).filter (fun m => ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p ∣ m)
  have hχ (z : ZMod 1) : (1:DirichletCharacter ℂ 1) z=1 := by
    rw [Subsingleton.elim z 1,map_one]
  have hB : roughCharacterIocSum (1:DirichletCharacter ℂ 1) (Nat.primesLE ⌊W⌋₊) 0 M =
      (B.card:ℂ) := by
    unfold roughCharacterIocSum
    simp_rw [hχ,mul_one]
    rw [← sum_filter,sum_const,nsmul_eq_mul,mul_one]
  have hh := hcount 1 (1:DirichletCharacter ℂ 1) (M:ℝ) (by simp) hM
  change ‖(V:ℂ)⁻¹*roughCharacterIocSum (1:DirichletCharacter ℂ 1)
    (Nat.primesLE ⌊W⌋₊) 0 ⌊(M:ℝ)⌋₊-
    (if (1:DirichletCharacter ℂ 1)=1 then ((⌊(M:ℝ)⌋₊:ℝ):ℂ) else 0)‖ ≤
      1*(M:ℝ)*L^(-(0:ℝ)) at hh
  rw [Nat.floor_natCast,hB,ite_eq_left rfl,neg_zero,Real.rpow_zero,one_mul,mul_one] at hh
  rw [← Complex.ofReal_natCast,← Complex.ofReal_inv,← Complex.ofReal_mul,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs] at hh
  have hf := (abs_le.mp hh).2
  have hle : V⁻¹*(B.card:ℝ) ≤ 2*(M:ℝ) := by linarith only [hf]
  rw [← div_eq_inv_mul] at hle
  exact (div_le_iff₀ (markedSieveEulerProduct_pos W)).mp hle

theorem giant_candidate_rough_dyad_card_eventually (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ N k : ℕ,
      let W := Real.exp ((Real.log x)^(6/25:ℝ))
      ((giantCandidateRoughDyad W (x^γ) N k).card:ℝ) ≤
        4*(2:ℝ)^k*markedSieveEulerProduct W := by
  have hτ : 0 < γ/2 := half_pos hγ
  filter_upwards [Real.tendsto_log_atTop.eventually (giant_candidate_rough_prefix_card_eventually (γ/2) hτ),
    prime_extraction_half_power_le_eventually hγ,eventually_gt_atTop (0:ℝ)] with x hprefix hhalf hx
  intro N k
  let W := Real.exp ((Real.log x)^(6/25:ℝ))
  let B := giantCandidateRoughDyad W (x^γ) N k
  change (B.card:ℝ) ≤ 4*(2:ℝ)^k*markedSieveEulerProduct W
  by_cases hB : B.Nonempty
  · obtain ⟨m,hm⟩ := hB
    obtain ⟨hb,hs⟩ := mem_filter.mp hm
    have hmhi : (m:ℝ) < 2*(2:ℝ)^k := by
      exact_mod_cast (primeExtractionDyadicBlock_bounds hb).2
    have hlarge : Real.exp ((γ/2)*Real.log x) ≤ ((2*2^k:ℕ):ℝ) := by
      have he : Real.exp ((γ/2)*Real.log x) = x^(γ/2) := by
        rw [Real.rpow_def_of_pos hx,mul_comm]
      rw [he]
      push_cast
      exact hhalf.trans (by
        have hh : x^γ < (m:ℝ) := hs.1
        linarith only [hh,hmhi])
    calc
      _ ≤ (((Ioc 0 (2*2^k)).filter (fun m => ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p ∣ m)).card:ℝ) :=
        Nat.cast_le.mpr (card_le_card (giantCandidateRoughDyad_subset_prefix W (x^γ) N k))
      _ ≤ 2*((2*2^k:ℕ):ℝ)*markedSieveEulerProduct W := hprefix _ hlarge
      _ = _ := by push_cast; ring
  · rw [not_nonempty_iff_eq_empty.mp hB,card_empty,Nat.cast_zero]
    exact mul_nonneg (by positivity) (markedSieveEulerProduct_pos W).le

end
end ArtinMatthews
