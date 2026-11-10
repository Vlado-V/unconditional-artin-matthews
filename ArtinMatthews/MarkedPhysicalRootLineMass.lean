module

public import ArtinMatthews.MarkedRootProjectiveCRT
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.Monotonicity.Lemmas
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

/-! Exact finite root-line masses. Every prime of the actual modulus is
charged once when the physical incidence conditions force its line.
Additional shared-prime conditions can only decrease this mass. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalRootLineMass (S : ℕ) : ℝ :=
  ∏ p : S.primeFactors, (1/((p : ℕ)+1 : ℝ))

theorem markedPhysicalRootLineMass_nonneg (S : ℕ) : 0 ≤ markedPhysicalRootLineMass S := by
  unfold markedPhysicalRootLineMass
  positivity

theorem markedPhysicalRootLineMass_eq (S : ℕ) :
    markedPhysicalRootLineMass S =
      1/((∏ p : S.primeFactors, ((p : ℕ)+1) : ℕ) : ℝ) := by
  simp [markedPhysicalRootLineMass, div_eq_mul_inv, Finset.prod_inv_distrib]

theorem markedPhysicalRoot_kernel_line_mass {S : ℕ} [NeZero S]
    (hS : Squarefree S) (ℓ : MarkedRootLineTuple S) :
    (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
      if markedRootKernelTuple hS g = ℓ then (1 : ℝ) else 0) /
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) =
      markedPhysicalRootLineMass S := by
  classical
  have hh := marked_squarefree_root_kernel_tuple_average hS
    (fun t => if t = ℓ then (1 : ℂ) else 0)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one] at hh
  have hs : (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
      if markedRootKernelTuple hS g = ℓ then (1 : ℂ) else 0) =
      ((∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
        if markedRootKernelTuple hS g = ℓ then (1 : ℝ) else 0) : ℝ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro g _
    split_ifs <;> rfl
  rw [hs] at hh
  rw [markedPhysicalRootLineMass_eq]
  have hr : (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)⁻¹ *
      (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
        if markedRootKernelTuple hS g = ℓ then (1 : ℝ) else 0) =
      (((∏ p : S.primeFactors, ((p : ℕ)+1) : ℕ) : ℝ))⁻¹ := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast] using hh
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hr

theorem markedPhysicalRoot_forced_line_count_le {S : ℕ} [NeZero S]
    (hS : Squarefree S) (E : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) → Prop)
    (ℓ : MarkedRootLineTuple S)
    (hE : ∀ g, E g → markedRootKernelTuple hS g = ℓ) :
    (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S), if E g then (1 : ℝ) else 0) /
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) ≤
      markedPhysicalRootLineMass S := by
  rw [← markedPhysicalRoot_kernel_line_mass hS ℓ]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro g _
  by_cases hg : E g
  · simp only [ite_eq_left hg, ite_eq_left (hE g hg), le_refl]
  · simp only [ite_eq_right hg]
    split_ifs <;> norm_num

theorem markedPhysicalRoot_forced_line_weighted_sum_le {ι : Type*}
    (I : Finset ι) {S : ℕ} [NeZero S] (hS : Squarefree S)
    (E : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) → ι → Prop)
    (ℓ : ι → MarkedRootLineTuple S) (w : ι → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i)
    (hE : ∀ i ∈ I, ∀ g, E g i → markedRootKernelTuple hS g = ℓ i) :
    (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
      ∑ i ∈ I, w i * (if E g i then (1 : ℝ) else 0)) /
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) ≤
      markedPhysicalRootLineMass S * ∑ i ∈ I, w i := by
  rw [Finset.sum_comm, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [← Finset.mul_sum, mul_div_assoc]
  apply (mul_le_mul_of_nonneg_left
    (markedPhysicalRoot_forced_line_count_le hS (fun g => E g i) (ℓ i) (hE i hi))
      (hw i hi)).trans_eq
  ring

end ArtinMatthews
