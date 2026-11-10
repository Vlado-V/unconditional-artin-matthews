module

public import ArtinMatthews.MarkedTypeIICommonQuotientCounts
public import ArtinMatthews.MarkedTypeIIArithmetic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
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


set_option backward.privateInPublic true
@[expose] public section

/-! For coprime last labels, the exact delta test is counted by its
common quotient. The actual progression divisor second moment controls
the count. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

def MarkedPhysicalScalarDelta (b a : ℕ) (v u : ℕ×ℕ) : Prop :=
  (b:ℤ)*v.1*v.2-(a:ℤ)*u.1*u.2=(b:ℤ)-(a:ℤ)

theorem markedPhysicalScalarDelta_count_le (S T : Finset ℕ) {a b Z : ℕ}
    {Y : ℝ} (hY : 0 < Y) (haY : Y ≤ (a:ℝ)) (hbY : Y ≤ (b:ℝ))
    (hcop : a.Coprime b) (haZ : a^4 ≤ Z) (hbZ : b^4 ≤ Z)
    (hR : ∀ v ∈ S.product T,v.1*v.2 ∈ Finset.Icc 1 Z) :
    (∑ v ∈ S.product T,∑ u ∈ S.product T,if MarkedPhysicalScalarDelta b a v u then (1:ℝ) else 0)
      ≤ 8*(Z:ℝ)/Y*(1+Real.log (Z:ℝ))^3 := by
  let R := S.product T
  let H := Finset.range Z
  let C := ∑ v ∈ R,∑ u ∈ R,if MarkedPhysicalScalarDelta b a v u then (1:ℝ) else 0
  have ha : 0 < a := by exact_mod_cast hY.trans_le haY
  have hprod (v : ℕ×ℕ) (hv : v ∈ R) : v.1*v.2 ≤ a*Z :=
    (Finset.mem_Icc.mp (hR v hv)).2.trans (by simpa only [one_mul] using Nat.mul_le_mul_right Z (show 1 ≤ a from ha))
  have hterm (v u : ℕ×ℕ) (hv : v ∈ R) (hu : u ∈ R) :
      Complex.ofReal (if MarkedPhysicalScalarDelta b a v u then 1 else 0) =
      ∑ h ∈ H,if v.1*v.2=1+a*h ∧ u.1*u.2=1+b*h then (1:ℂ) else 0 := by
    have he := marked_commonQuotient_sum_of_mul_bound (H := Z) ha hcop
      (Finset.mem_Icc.mp (hR v hv)).1 (Finset.mem_Icc.mp (hR u hu)).1 (hprod v hv) 1
    simpa only [MarkedPhysicalScalarDelta,Nat.cast_mul,mul_assoc,apply_ite,
      Complex.ofReal_one,Complex.ofReal_zero] using he.symm
  have hc : (C:ℂ) =
      ∑ h ∈ H,markedTypeIIQuotientCoefficient S T (fun _ => 1) (fun _ => 1) a h*
        conj (markedTypeIIQuotientCoefficient S T (fun _ => 1) (fun _ => 1) b h) := by
    calc
      _ = ∑ v ∈ R,∑ u ∈ R,∑ h ∈ H,
          if v.1*v.2=1+a*h ∧ u.1*u.2=1+b*h then (1:ℂ) else 0 := by
        simp only [C,Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro v hv
        exact Finset.sum_congr rfl (fun u hu => hterm v u hv hu)
      _ = _ := by
        simp_rw [Finset.sum_comm (s := R) (t := H)]
        apply Finset.sum_congr rfl
        intro h _
        simp only [markedTypeIIQuotientCoefficient,markedTypeIIProductFiber,Finset.sum_filter,
          mul_one,map_sum,apply_ite (conj : ℂ →+* ℂ),map_one,map_zero]
        simp_rw [Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro u _
        by_cases hv : v.1*v.2=1+a*h <;> by_cases hu : u.1*u.2=1+b*h <;> simp [hv,hu]
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hq := markedTypeII_common_quotient_pair_norm_le S T H (fun _ => (1:ℂ)) (fun _ => (1:ℂ))
    zero_le_one zero_le_one hY (fun _ _ => by simp) (fun _ _ => by simp)
    haY hbY haZ hbZ (fun v hv => (Finset.mem_Icc.mp (hR v hv)).2)
  change C ≤ _
  simpa only [Complex.star_def,← hc,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC,
    mul_one,one_pow,one_mul] using hq

end
end ArtinMatthews
