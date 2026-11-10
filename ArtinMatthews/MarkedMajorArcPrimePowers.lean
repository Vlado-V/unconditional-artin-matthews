module

public import ArtinMatthews.MarkedMajorArcMangoldt
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! Actual removal of higher prime powers from the twisted Mangoldt interval
sum using Mathlib's proved Chebyshev remainder bound. -/
namespace ArtinMatthews

open Finset ArithmeticFunction OAI.TwoPointCorrelations
open scoped BigOperators

lemma marked_major_mangoldt_norm_vonMangoldt {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖markedMajorMangoldt χ t n‖ ≤ vonMangoldt n / n := by
  rw [markedMajorMangoldt,norm_mul,Complex.norm_natCast_cpow_of_pos hn]
  have hre : (-(1-(t:ℂ)*Complex.I)).re = -1 := by simp
  rw [hre,Real.rpow_neg_one,mrtCharacterMangoldtTwist,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one _))
    (by positivity)).trans_eq (by ring)

/-- The actual normalized prime-power remainder on any sharp interval. -/
theorem marked_major_prime_power_interval_error {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    ‖(∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, markedMajorMangoldt χ t n) -
      ∑ n ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, markedMajorMangoldt χ t n‖ ≤
      (2*Real.sqrt v*Real.log v)/u := by
  classical
  let S := Ioc ⌊u⌋₊ ⌊v⌋₊
  have hu0 : 0 < u := by linarith
  have hv : 1 ≤ v := hu.trans huv
  have he : (∑ n ∈ S, markedMajorMangoldt χ t n) -
      ∑ n ∈ S.filter Nat.Prime, markedMajorMangoldt χ t n =
      ∑ n ∈ S.filter (fun n => ¬n.Prime), markedMajorMangoldt χ t n := by
    have hh := sum_filter_add_sum_filter_not S Nat.Prime (markedMajorMangoldt χ t)
    linear_combination -hh
  change ‖(∑ n ∈ S, markedMajorMangoldt χ t n) -
      ∑ n ∈ S.filter Nat.Prime, markedMajorMangoldt χ t n‖ ≤ _
  rw [he]
  have hnorm (n : ℕ) (hn : n ∈ S) : ‖markedMajorMangoldt χ t n‖ ≤ vonMangoldt n/u := by
    have hnlo : u < (n:ℝ) := (Nat.floor_lt hu0.le).mp (mem_Ioc.mp hn).1
    have hnp : (0:ℝ) < n := hu0.trans hnlo
    exact (marked_major_mangoldt_norm_vonMangoldt χ t (by exact_mod_cast hnp)).trans
      (div_le_div_of_nonneg_left vonMangoldt_nonneg hu0 hnlo.le)
  have hsubset : S.filter (fun n => ¬n.Prime) ⊆
      (Ioc 0 ⌊v⌋₊).filter (fun n => ¬n.Prime) := by
    intro n hn
    obtain ⟨hnS,hnP⟩ := mem_filter.mp hn
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hnS
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,hhi⟩,hnP⟩
  calc
    _ ≤ ∑ n ∈ S.filter (fun n => ¬n.Prime), ‖markedMajorMangoldt χ t n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S.filter (fun n => ¬n.Prime), vonMangoldt n/u :=
      sum_le_sum (fun n hn => hnorm n (mem_filter.mp hn).1)
    _ = (∑ n ∈ S.filter (fun n => ¬n.Prime), vonMangoldt n)/u := by rw [sum_div]
    _ ≤ (∑ n ∈ (Ioc 0 ⌊v⌋₊).filter (fun n => ¬n.Prime), vonMangoldt n)/u :=
      div_le_div_of_nonneg_right
        (sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => vonMangoldt_nonneg)) hu0.le
    _ = (Chebyshev.psi v-Chebyshev.theta v)/u := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    _ ≤ _ := div_le_div_of_nonneg_right (Chebyshev.psi_sub_theta_le hv) hu0.le

lemma marked_major_mangoldt_prime_term {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {p : ℕ} (hp : p.Prime) :
    markedMajorMangoldt χ t p =
      χ (p:ZMod q)*(Real.log p:ℂ)*(p:ℂ)^(-1+(t:ℂ)*Complex.I) := by
  rw [markedMajorMangoldt,mrtCharacterMangoldtTwist,vonMangoldt_apply_prime hp]
  congr 1
  congr 1
  ring

end ArtinMatthews
