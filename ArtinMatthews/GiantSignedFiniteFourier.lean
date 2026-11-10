module

public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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

/-! Counting-measure Fourier identities for the actual finite residue
fibers of the full memory space. -/
namespace ArtinMatthews
open scoped BigOperators ComplexConjugate
noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G]

def giantSignedFourier (f : G → ℂ) (χ : AddChar G ℂ) : ℂ :=
  ∑ x, χ (-x) * f x

theorem giantSignedFourier_pairing (f h : G → ℂ) :
    (∑ χ : AddChar G ℂ, giantSignedFourier f χ * star (giantSignedFourier h χ)) =
      (Fintype.card G : ℂ) * ∑ x, f x * star (h x) := by
  classical
  have hp (χ : AddChar G ℂ) (x y : G) :
      (χ (-x) * f x) * star (χ (-y) * h y) = χ (y - x) * (f x * star (h y)) := by
    have hc : star (χ (-y)) = χ y := by
      simpa only [neg_neg, Complex.star_def] using (AddChar.map_neg_eq_conj χ (-y)).symm
    rw [star_mul, hc, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp only [giantSignedFourier, star_sum, Finset.sum_mul, Finset.mul_sum, hp]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (AddChar G ℂ)))]
  simp only [← Finset.sum_mul, AddChar.sum_apply_eq_ite, sub_eq_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem giantSignedFourier_parseval (f : G → ℂ) :
    (∑ χ : AddChar G ℂ, ‖giantSignedFourier f χ‖ ^ 2) =
      (Fintype.card G : ℝ) * ∑ x, ‖f x‖ ^ 2 := by
  have h := giantSignedFourier_pairing f f
  simp only [Complex.star_def, Complex.mul_conj'] at h
  exact_mod_cast h

theorem giantSignedFourier_translate (f : G → ℂ) (d : G) (χ : AddChar G ℂ) :
    giantSignedFourier (fun x => f (x + d)) χ = χ d * giantSignedFourier f χ := by
  classical
  unfold giantSignedFourier
  calc
    _ = ∑ y : G, χ (d - y) * f y := by
      refine Fintype.sum_equiv (Equiv.addRight d) _ _ ?_
      intro x
      change χ (-x) * f (x + d) = χ (d - (x + d)) * f (x + d)
      rw [show d - (x + d) = -x by abel]
    _ = _ := by
      simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, mul_assoc]
      rw [Finset.mul_sum]

def giantSignedCharacterPhase (χ : AddChar G ℂ) (u : G) : ℝ :=
  Complex.arg (χ u) / (2 * Real.pi)

theorem giantSignedCharacterPhase_exp (χ : AddChar G ℂ) (u : G) :
    Complex.exp (2 * Real.pi * Complex.I * (giantSignedCharacterPhase χ u : ℂ)) = χ u := by
  have h := Complex.norm_mul_exp_arg_mul_I (χ u)
  rw [χ.norm_apply, Complex.ofReal_one, one_mul] at h
  convert h using 1
  unfold giantSignedCharacterPhase
  push_cast
  field_simp

theorem giantSignedCharacterPhase_zsmul (χ : AddChar G ℂ) (u : G) (n : ℤ) :
    χ (n • u) =
      Complex.exp (2 * Real.pi * Complex.I * (giantSignedCharacterPhase χ u : ℂ) * (n : ℂ)) := by
  rw [AddChar.map_zsmul_eq_zpow, ← giantSignedCharacterPhase_exp χ u, ← Complex.exp_int_mul]
  congr 1
  ring

end
end ArtinMatthews
