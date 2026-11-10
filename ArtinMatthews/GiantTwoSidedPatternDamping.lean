module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

/-! The endpoint count and its half-damping have a uniform bound when
only a bounded number of slots are free. The bound has no dependence
on the number of copied slots. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem exists_giantTwoSidedPattern_slot_bound {q v : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hv : 0 < v) (s : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ (V : ℝ) (z t : ℕ),v ≤ V → t ≤ s →
      (V⁻¹)^t*((z:ℝ)+(t:ℝ))^t*q^((z:ℝ)/2) ≤ C := by
  let a := -Real.log q/2
  let B := max 1 v⁻¹
  let D := (s.factorial:ℝ)/a^s
  have ha : 0 < a := div_pos (neg_pos.mpr (Real.log_neg hq hq1)) (by norm_num)
  have hB : 1 ≤ B := le_max_left _ _
  have hD : 0 ≤ D := by positivity
  refine ⟨max 1 (B^s*((s:ℝ)+1)^s*D*Real.exp a),le_max_left _ _,?_⟩
  intro V z t hV ht
  have hV0 := hv.trans_le hV
  have hVpow : (V⁻¹)^t ≤ B^s :=
    (pow_le_pow_left₀ (inv_nonneg.mpr hV0.le)
      ((inv_anti₀ hv hV).trans (le_max_right _ _)) t).trans (pow_le_pow_right₀ hB ht)
  let y := (z:ℝ)+1
  let W := ((s:ℝ)+1)*y
  have hy : 1 ≤ y := le_add_of_nonneg_left (Nat.cast_nonneg z)
  have hW : 1 ≤ W := one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (Nat.cast_nonneg s)) hy
  have hbase : (z:ℝ)+(t:ℝ) ≤ W := by
    unfold W y
    have hts : (t:ℝ)≤(s:ℝ) := Nat.cast_le.mpr ht
    nlinarith only [hts,mul_nonneg (Nat.cast_nonneg s : (0:ℝ) ≤ (s:ℝ)) (Nat.cast_nonneg z : (0:ℝ)≤z)]
  have hcount : ((z:ℝ)+(t:ℝ))^t ≤ ((s:ℝ)+1)^s*y^s := by
    rw [← mul_pow]
    exact (pow_le_pow_left₀ (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hbase t).trans
      (pow_le_pow_right₀ hW ht)
  have hphase : q^((z:ℝ)/2) = Real.exp (-(a*(z:ℝ))) := by
    rw [Real.rpow_def_of_pos hq]
    congr 1
    unfold a
    ring
  have hdecay : y^s*Real.exp (-(a*(z:ℝ))) ≤ D*Real.exp a := by
    have he := Real.pow_div_factorial_le_exp (a*y) (mul_nonneg ha.le (zero_le_one.trans hy)) s
    calc
      _ = ((a*y)^s/(s.factorial:ℝ))*D*Real.exp (-(a*(z:ℝ))) := by
        unfold D
        rw [mul_pow]
        field_simp [ha.ne',Nat.cast_ne_zero.mpr (Nat.factorial_pos s).ne']
      _ ≤ Real.exp (a*y)*D*Real.exp (-(a*(z:ℝ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hD) (Real.exp_nonneg _)
      _ = _ := by
        rw [mul_right_comm,← Real.exp_add,show a*y + -(a*(z:ℝ)) = a by unfold y; ring,mul_comm]
  calc
    _ ≤ B^s*(((s:ℝ)+1)^s*y^s)*q^((z:ℝ)/2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hVpow hcount (by positivity) (by positivity))
        (Real.rpow_nonneg hq.le _)
    _ = (B^s*((s:ℝ)+1)^s)*(y^s*Real.exp (-(a*(z:ℝ)))) := by rw [hphase]; ring
    _ ≤ (B^s*((s:ℝ)+1)^s)*(D*Real.exp a) := mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ ≤ _ := by rw [← mul_assoc]; exact le_max_right _ _

end
end ArtinMatthews
