module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# Actual Atkin-Lehner matrix arithmetic at the cusp 1/s

For `r*a-s*b=1`, the integer matrix `[r,b;rs,ra]` has determinant `r`.
Its normalization by `sqrt(r)` is the Atkin-Lehner scaling at `1/s`.
The explicit integer conjugates below prove the arithmetic normalizer property;
they use no trace formula or bound for exponential sums.
-/

namespace ArtinMatthews

open Matrix

def atkinNumerator (r s a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![r,b;r*s,r*a]

def atkinGammaMatrix (r s A B C D : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![A,B;r*s*C,D]

def atkinGammaForward (r s a b A B C D : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![r*a*A-r*s*b*C+r*a*s*B-s*b*D,
     a*b*A-s*b^2*C+r*a^2*B-a*b*D;
     r*s*(-A+r*C-s*B+D),
     -s*b*A+r*s*b*C-r*s*a*B+r*a*D]

def atkinGammaBackward (r s a b A B C D : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![r*a*A+r*s*a*b*C-r*s*B-s*b*D,
     -b*A-s*b^2*C+r*B+b*D;
     r*s*(a*A+r*a^2*C-s*B-a*D),
     -s*b*A-r*s*a*b*C+r*s*B+r*a*D]

theorem atkinNumerator_det (r s a b : ℤ) :
    (atkinNumerator r s a b).det = r*(r*a-s*b) := by
  simp only [atkinNumerator,Matrix.det_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Matrix.of_apply]
  ring

theorem atkinGammaMatrix_det (r s A B C D : ℤ) :
    (atkinGammaMatrix r s A B C D).det = A*D-r*s*B*C := by
  simp only [atkinGammaMatrix,Matrix.det_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Matrix.of_apply]
  ring

theorem atkinGammaForward_det (r s a b A B C D : ℤ) :
    (atkinGammaForward r s a b A B C D).det =
      (r*a-s*b)^2*(A*D-r*s*B*C) := by
  simp only [atkinGammaForward,Matrix.det_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Matrix.of_apply]
  ring

theorem atkinGammaBackward_det (r s a b A B C D : ℤ) :
    (atkinGammaBackward r s a b A B C D).det =
      (r*a-s*b)^2*(A*D-r*s*B*C) := by
  simp only [atkinGammaBackward,Matrix.det_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Matrix.of_apply]
  ring

/-- Literal integral multiplication identity for the forward conjugation. -/
theorem atkinGammaForward_mul (r s a b A B C D : ℤ) :
    atkinNumerator r s a b * atkinGammaForward r s a b A B C D =
      (r*a-s*b) • (atkinGammaMatrix r s A B C D * atkinNumerator r s a b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinNumerator,atkinGammaForward,atkinGammaMatrix,Matrix.mul_apply,Fin.sum_univ_two]
    <;> ring

/-- Literal integral multiplication identity for the reverse conjugation. -/
theorem atkinGammaBackward_mul (r s a b A B C D : ℤ) :
    atkinGammaBackward r s a b A B C D * atkinNumerator r s a b =
      (r*a-s*b) • (atkinNumerator r s a b * atkinGammaMatrix r s A B C D) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinNumerator,atkinGammaBackward,atkinGammaMatrix,Matrix.mul_apply,Fin.sum_univ_two]
    <;> ring

/-- The actual normalized scaling matrix, with the square root kept explicit. -/
noncomputable def atkinScalingMatrix (r : ℕ) (s a b : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1/Real.sqrt (r : ℝ)) • (atkinNumerator (r : ℤ) s a b).map (fun z : ℤ => (z : ℝ))

theorem atkinScalingMatrix_det {r : ℕ} (hr : 0 < r) {s a b : ℤ}
    (hab : (r : ℤ)*a-s*b = 1) : (atkinScalingMatrix r s a b).det = 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have ht : Real.sqrt (r : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hrR).ne'
  have habR : (r : ℝ)*(a : ℝ)-(s : ℝ)*(b : ℝ) = 1 := by exact_mod_cast hab
  rw [atkinScalingMatrix,Matrix.det_smul]
  simp only [Matrix.det_fin_two,atkinNumerator,Matrix.map_apply,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Fintype.card_fin,Int.cast_mul,Int.cast_natCast]
  change (1/Real.sqrt (r : ℝ))^2 *
    ((r : ℝ)*((r : ℝ)*(a : ℝ))-(b : ℝ)*((r : ℝ)*(s : ℝ))) = 1
  have heq : (r : ℝ)*((r : ℝ)*(a : ℝ))-(b : ℝ)*((r : ℝ)*(s : ℝ)) = r := by
    calc
      _ = (r : ℝ)*((r : ℝ)*(a : ℝ)-(s : ℝ)*(b : ℝ)) := by ring
      _ = (r : ℝ) := by rw [habR,mul_one]
  rw [heq]
  rw [div_pow,one_pow,Real.sq_sqrt hrR.le]
  exact div_mul_cancel₀ 1 hrR.ne'

/-- A determinant-one scaling, rather than an unnormalized rational matrix. -/
noncomputable def atkinScaling {r : ℕ} (hr : 0 < r) {s a b : ℤ}
    (hab : (r : ℤ)*a-s*b = 1) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨atkinScalingMatrix r s a b,atkinScalingMatrix_det hr hab⟩

theorem atkinScaling_cusp_ratio {r : ℕ} (hr : 0 < r) {s a b : ℤ}
    (hab : (r : ℤ)*a-s*b = 1) :
    (atkinScaling hr hab) 0 0 / (atkinScaling hr hab) 1 0 = 1/(s : ℝ) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have ht : Real.sqrt (r : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hr)).ne'
  change ((1/Real.sqrt (r : ℝ))*(r : ℝ))/
    ((1/Real.sqrt (r : ℝ))*(((r : ℤ)*s : ℤ) : ℝ)) = 1/(s : ℝ)
  rw [Int.cast_mul,Int.cast_natCast]
  by_cases hs : (s : ℝ) = 0
  · simp [hs]
  · field_simp

/-- The actual real scaling intertwines the integral forward conjugate. -/
theorem atkinScalingMatrix_forward {r : ℕ} {s a b : ℤ}
    (hab : (r : ℤ)*a-s*b = 1) (A B C D : ℤ) :
    atkinScalingMatrix r s a b *
        (atkinGammaForward (r : ℤ) s a b A B C D).map (fun z : ℤ => (z : ℝ)) =
      (atkinGammaMatrix (r : ℤ) s A B C D).map (fun z : ℤ => (z : ℝ)) *
        atkinScalingMatrix r s a b := by
  have hi := atkinGammaForward_mul (r : ℤ) s a b A B C D
  rw [hab,one_smul] at hi
  have hm := congrArg (Int.castRingHom ℝ).mapMatrix hi
  simp only [map_mul] at hm
  dsimp only [atkinScalingMatrix]
  rw [Matrix.smul_mul,Matrix.mul_smul]
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => (1/Real.sqrt (r : ℝ)) • M) hm

/-- The reverse integral conjugate uses the same genuine normalized scaling. -/
theorem atkinScalingMatrix_backward {r : ℕ} {s a b : ℤ}
    (hab : (r : ℤ)*a-s*b = 1) (A B C D : ℤ) :
    (atkinGammaBackward (r : ℤ) s a b A B C D).map (fun z : ℤ => (z : ℝ)) *
        atkinScalingMatrix r s a b =
      atkinScalingMatrix r s a b *
        (atkinGammaMatrix (r : ℤ) s A B C D).map (fun z : ℤ => (z : ℝ)) := by
  have hi := atkinGammaBackward_mul (r : ℤ) s a b A B C D
  rw [hab,one_smul] at hi
  have hm := congrArg (Int.castRingHom ℝ).mapMatrix hi
  simp only [map_mul] at hm
  dsimp only [atkinScalingMatrix]
  rw [Matrix.smul_mul,Matrix.mul_smul]
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => (1/Real.sqrt (r : ℝ)) • M) hm

end ArtinMatthews
