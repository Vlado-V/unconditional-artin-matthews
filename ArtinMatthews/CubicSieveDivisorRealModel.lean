module

public import ArtinMatthews.CubicSieveDivisorUnitModel
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The logarithmic prefix model at a real cutoff and its exact density. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveDivisorUnitDensity (d : ℕ) (x : ℝ) : ℝ :=
  ((Real.log x + 2 * Real.eulerMascheroniConstant) * cubicSieveCoprimeDensity d -
    2 * cubicSieveCoprimeLogMoment d) / (d : ℝ)

theorem cubicSieve_divisorUnitModel_hasDerivAt (d : ℕ) (hd : 0 < d) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (cubicSieveDivisorUnitModel d) (cubicSieveDivisorUnitDensity d x) x := by
  have hlog : HasDerivAt (fun t => Real.log t + (2 * Real.eulerMascheroniConstant - 1)) x⁻¹ x :=
    (Real.hasDerivAt_log hx.ne').add_const _
  have h := ((hasDerivAt_id x).div_const (d : ℝ)).mul
    ((hlog.mul_const (cubicSieveCoprimeDensity d)).sub_const (2 * cubicSieveCoprimeLogMoment d))
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  convert h using 1
  · funext t
    simp only [cubicSieveDivisorUnitModel, Pi.mul_apply, id_eq]
    ring
  · simp only [cubicSieveDivisorUnitDensity, id_eq]
    field_simp [hx.ne', hd']
    ring

theorem cubicSieve_coprimeLogMoment_abs_le {d : ℕ} (hd : 0 < d) :
    |cubicSieveCoprimeLogMoment d| ≤ (2 : ℝ) ^ d.primeFactors.card * Real.log (d : ℝ) := by
  unfold cubicSieveCoprimeLogMoment
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _T ∈ d.primeFactors.powerset, Real.log (d : ℝ) := by
      apply sum_le_sum
      intro T hT
      let a := roughSubsetDivisor T
      have hP (p : ℕ) (hp : p ∈ T) : p.Prime :=
        Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp)
      have hapos := roughSubsetDivisor_pos T hP
      have hadvd : a ∣ d := (roughSubsetDivisor_dvd_iff T d hP).mpr
        (fun _ hp => Nat.dvd_of_mem_primeFactors (mem_powerset.mp hT hp))
      have ha : (1 : ℝ) ≤ a := by exact_mod_cast hapos
      have ha₀ : (0 : ℝ) < a := zero_lt_one.trans_le ha
      have had : (a : ℝ) ≤ d := Nat.cast_le.mpr (Nat.le_of_dvd hd hadvd)
      change |((-1 : ℝ) ^ T.card / (a : ℝ)) * Real.log (a : ℝ)| ≤ _
      simp only [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos ha₀,
        abs_of_nonneg (Real.log_nonneg ha)]
      exact (mul_le_of_le_one_left (Real.log_nonneg ha) ((div_le_one ha₀).mpr ha)).trans
        (Real.log_le_log ha₀ had)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_powerset, Nat.cast_pow, Nat.cast_ofNat]

private theorem cubicSieve_log_le_sqrt_twice {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hx)
  calc
    _ = 2 * Real.log (Real.sqrt x) := by
      conv_lhs => rw [← Real.sq_sqrt hx.le, Real.log_pow, Nat.cast_ofNat]
    _ ≤ _ := by linarith only [h]

theorem cubicSieve_divisorUnitDensity_bound {d : ℕ} (hd : 0 < d) {x t : ℝ}
    (hdx : (d : ℝ) ≤ x) (ht : 1 ≤ t) (htx : t ≤ x) :
    |cubicSieveDivisorUnitDensity d t| ≤ 8 * (2 : ℝ) ^ d.primeFactors.card * Real.sqrt x := by
  let D := (2 : ℝ) ^ d.primeFactors.card
  let A := cubicSieveCoprimeDensity d
  let B := cubicSieveCoprimeLogMoment d
  have hD : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd₀ : (0 : ℝ) < d := zero_lt_one.trans_le hd₁
  have hlogd := Real.log_le_log hd₀ hdx
  have ht₀ := zero_lt_one.trans_le ht
  have hx := ht₀.trans_le htx
  have hlogt := Real.log_le_log ht₀ htx
  have hlogx := cubicSieve_log_le_sqrt_twice hx
  have hs₁ : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr (ht.trans htx)
  have hs₀ := Real.sqrt_nonneg x
  have hγ₀ := Real.one_half_lt_eulerMascheroniConstant
  have hγ₁ := Real.eulerMascheroniConstant_lt_two_thirds
  obtain ⟨hA₀, hA₁⟩ : 0 ≤ A ∧ A ≤ 1 := cubicSieve_coprimeDensity_bounds hd.ne'
  have hB : |B| ≤ D * (2 * Real.sqrt x) :=
    (cubicSieve_coprimeLogMoment_abs_le hd).trans
      (mul_le_mul_of_nonneg_left (hlogd.trans hlogx) (zero_le_one.trans hD))
  have hp : 0 ≤ Real.log t + 2 * Real.eulerMascheroniConstant := by
    linarith only [Real.log_nonneg ht, hγ₀]
  have hp' : Real.log t + 2 * Real.eulerMascheroniConstant ≤ 4 * Real.sqrt x := by
    linarith only [hlogt, hlogx, hγ₁, hs₁]
  change |((Real.log t + 2 * Real.eulerMascheroniConstant) * A - 2 * B) / (d : ℝ)| ≤
    8 * D * Real.sqrt x
  rw [abs_div, abs_of_pos hd₀]
  calc
    _ ≤ |(Real.log t + 2 * Real.eulerMascheroniConstant) * A - 2 * B| :=
      div_le_self (abs_nonneg _) hd₁
    _ ≤ |(Real.log t + 2 * Real.eulerMascheroniConstant) * A| + |2 * B| := abs_sub _ _
    _ ≤ 4 * Real.sqrt x + 4 * D * Real.sqrt x := by
      simp only [abs_mul, abs_of_nonneg hp, abs_of_nonneg hA₀, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hfirst := (mul_le_of_le_one_right hp hA₁).trans hp'
      have hsecond := mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 2)
      linarith only [hfirst, hsecond]
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hD hs₀]

theorem cubicSieve_divisorUnitCount_real_model_error {d : ℕ} (hd : 0 < d) {x : ℝ}
    (hdx : (d : ℝ) ^ 2 ≤ x) (u : (ZMod d)ˣ) :
    |cubicSieveDivisorUnitCount d ⌊x⌋₊ u - cubicSieveDivisorUnitModel d x| ≤
      34 * (2 : ℝ) ^ d.primeFactors.card * Real.sqrt x := by
  let n := ⌊x⌋₊
  let D := (2 : ℝ) ^ d.primeFactors.card
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd₀ : (0 : ℝ) < d := zero_lt_one.trans_le hd₁
  have hx : 0 < x := (pow_pos hd₀ 2).trans_le hdx
  have hnsq : d ≤ n.sqrt := Nat.le_sqrt'.mpr
    (Nat.le_floor (by simpa only [Nat.cast_pow] using hdx))
  have hn : (d : ℝ) ≤ n := Nat.cast_le.mpr (hnsq.trans (Nat.sqrt_le_self n))
  have hn₁ : (1 : ℝ) ≤ n := hd₁.trans hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx.le
  have hsq : (n.sqrt : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (Nat.cast_nonneg _) hx.le).mpr
      ((by exact_mod_cast Nat.sqrt_le' n : (n.sqrt : ℝ) ^ 2 ≤ n).trans hnx)
  have h₁ := (cubicSieve_divisorUnitCount_model_error hd hnsq u).trans
    (mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 26 * D))
  have h₂ : |cubicSieveDivisorUnitModel d n - cubicSieveDivisorUnitModel d x| ≤
      8 * D * Real.sqrt x := by
    rw [abs_sub_comm]
    have hDiff (t : ℝ) (ht : t ∈ Set.Icc (n : ℝ) x) :
        HasDerivAt (cubicSieveDivisorUnitModel d) (cubicSieveDivisorUnitDensity d t) t :=
      cubicSieve_divisorUnitModel_hasDerivAt d hd (zero_lt_one.trans_le (hn₁.trans ht.1))
    have h := (convex_Icc (n : ℝ) x).norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (hDiff t ht).differentiableAt)
      (fun t ht => by
        rw [(hDiff t ht).deriv, Real.norm_eq_abs]
        exact cubicSieve_divisorUnitDensity_bound hd (hn.trans hnx) (hn₁.trans ht.1) ht.2)
      (Set.left_mem_Icc.mpr hnx) (Set.right_mem_Icc.mpr hnx)
    simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hnx)] at h
    exact h.trans (mul_le_of_le_one_right (by positivity) (by
      have hfloor := Nat.lt_floor_add_one x
      change x < (n : ℝ) + 1 at hfloor
      linarith only [hfloor]))
  exact (abs_sub_le _ (cubicSieveDivisorUnitModel d n) _).trans
    ((add_le_add h₁ h₂).trans_eq (by ring))

end ArtinMatthews
