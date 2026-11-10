module

public import ArtinMatthews.GaussianCoordinateFiniteSieve
public import ArtinMatthews.GaussianCoordinateModularSieve
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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


set_option backward.privateInPublic true
@[expose] public section

/-! Choosing the Gaussian parameter in the genuine coordinate sieve. The
constant remains explicit in the dimension, with scale H^n+Q^n. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open scoped BigOperators
noncomputable section
variable {β ι : Type*} [Fintype β]

private theorem nonneg_add_pow_bound {H Q : ℝ} (hH : 0 ≤ H) (hQ : 0 ≤ Q) (n : ℕ) :
    (H+Q)^n ≤ 2^n*(H^n+Q^n) := by
  by_cases h : H ≤ Q
  · calc
      (H+Q)^n ≤ (2*Q)^n := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = 2^n*Q^n := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg hH n)) (by positivity)
  · have h' : Q ≤ H := (lt_of_not_ge h).le
    calc
      (H+Q)^n ≤ (2*H)^n := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = 2^n*H^n := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg hQ n)) (by positivity)

def coordinateOptimizedSieveConstant (β : Type*) [Fintype β] : ℝ :=
  Real.exp Real.pi * coordinateGaussianConstant β * 2^(Fintype.card β)

theorem coordinateOptimizedSieveConstant_pos : 0 < coordinateOptimizedSieveConstant β := by
  unfold coordinateOptimizedSieveConstant
  exact mul_pos (mul_pos (Real.exp_pos _) coordinateGaussianConstant_pos) (by positivity)

theorem coordinateAdditiveSieveBound_optimized {H Q : ℝ} (hH : 0 < H) (hQ : 0 ≤ Q) :
    coordinateAdditiveSieveBound β Q (1/H^2) (H^2) ≤
      coordinateOptimizedSieveConstant β*(H^(Fintype.card β)+Q^(Fintype.card β)) := by
  have hs : Real.sqrt (1/H^2) = 1/H := by
    rw [Real.sqrt_div (by norm_num),Real.sqrt_one,Real.sqrt_sq hH.le]
  have hroot : H ≤ Real.sqrt (Real.pi/(1/H^2)) := by
    apply (Real.le_sqrt hH.le (by positivity)).mpr
    rw [div_div_eq_mul_div,div_one]
    nlinarith [Real.pi_gt_three,sq_nonneg H]
  have hq : Q/Real.sqrt (Real.pi/(1/H^2)) ≤ Q/H :=
    div_le_div_of_nonneg_left hQ hH hroot
  have harg : Real.pi*(1/H^2)*(H^2) = Real.pi := by field_simp
  unfold coordinateAdditiveSieveBound
  rw [harg,hs,one_div_one_div]
  have hp : (1+Q/Real.sqrt (Real.pi/(1/H^2)))^(Fintype.card β) ≤
      (1+Q/H)^(Fintype.card β) := pow_le_pow_left₀ (by positivity) (by linarith) _
  calc
    _ ≤ Real.exp Real.pi * (H^(Fintype.card β) *
        (coordinateGaussianConstant β*(1+Q/H)^(Fintype.card β))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hp coordinateGaussianConstant_pos.le) (by positivity))
          (Real.exp_pos _).le
    _ = (Real.exp Real.pi*coordinateGaussianConstant β)*(H+Q)^(Fintype.card β) := by
      rw [show H+Q = H*(1+Q/H) by field_simp,mul_pow]
      ring
    _ ≤ (Real.exp Real.pi*coordinateGaussianConstant β)*
        (2^(Fintype.card β)*(H^(Fintype.card β)+Q^(Fintype.card β))) :=
      mul_le_mul_of_nonneg_left (nonneg_add_pow_bound hH.le hQ _)
        (mul_pos (Real.exp_pos _) coordinateGaussianConstant_pos).le
    _ = _ := by unfold coordinateOptimizedSieveConstant; ring

theorem coordinate_modular_primal_sieve_optimized {Q H : ℝ} (hQ : 1 ≤ Q) (hH : 0 < H)
    (P : Finset ι) (x : ι → β → ℝ)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ∀ k : β → ℤ,
      1/Q ≤ ‖(fun b => x i b-x j b+(k b:ℝ))‖)
    (N : Finset (β → ℤ)) (hN : ∀ n ∈ N, (∑ b, (n b:ℝ)^2) ≤ H^2)
    (v : (β → ℤ) → ℂ) :
    (∑ p ∈ P, ‖∑ n ∈ N, v n*coordinatePhase (x p) n‖^2) ≤
      (coordinateOptimizedSieveConstant β*(H^(Fintype.card β)+Q^(Fintype.card β)))*
        ∑ n ∈ N, ‖v n‖^2 := by
  apply (coordinate_modular_primal_sieve (a := 1/H^2) hQ (by positivity) P x hsep N hN v).trans
  exact mul_le_mul_of_nonneg_right (coordinateAdditiveSieveBound_optimized hH (by linarith))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end
end ArtinMatthews.VaryingKummerAnalytic
