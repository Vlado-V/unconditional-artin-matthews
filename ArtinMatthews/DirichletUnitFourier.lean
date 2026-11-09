module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Finset
open scoped BigOperators
noncomputable section

variable (r : ℕ) [NeZero r]

def dirichletUnitFourierCoefficient (f : (ZMod r)ˣ → ℂ)
    (χ : DirichletCharacter ℂ r) : ℂ :=
  (r.totient : ℂ)⁻¹ * ∑ a : (ZMod r)ˣ, f a * star (χ (a : ZMod r))

theorem dirichletUnitFourier_orthogonality (a b : (ZMod r)ˣ) :
    (∑ χ : DirichletCharacter ℂ r,
      star (χ (a : ZMod r)) * χ (b : ZMod r)) =
      if a = b then (r.totient : ℂ) else 0 := by
  classical
  have hstar (χ : DirichletCharacter ℂ r) :
      star (χ (a : ZMod r)) = χ ((a : ZMod r)⁻¹) := by
    rw [MulChar.star_apply', MulChar.inv_apply]
    simp only [Ring.inverse_unit, ZMod.inv_coe_unit]
  simp_rw [hstar]
  simpa only [Units.val_inj] using
    DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit (b : ZMod r)

theorem dirichletUnitFourier_inversion (f : (ZMod r)ˣ → ℂ) (b : (ZMod r)ˣ) :
    (∑ χ : DirichletCharacter ℂ r,
      dirichletUnitFourierCoefficient r f χ * χ (b : ZMod r)) = f b := by
  classical
  have hr : (r.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos r)).ne'
  calc
    _ = (r.totient : ℂ)⁻¹ * ∑ a : (ZMod r)ˣ, f a *
        (∑ χ : DirichletCharacter ℂ r,
          star (χ (a : ZMod r)) * χ (b : ZMod r)) := by
      simp only [dirichletUnitFourierCoefficient, Finset.mul_sum,
        Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = f b := by
      simp_rw [dirichletUnitFourier_orthogonality]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', mem_univ, ite_true]
      field_simp

theorem dirichletUnitFourier_parseval (f : (ZMod r)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ r,
      ‖dirichletUnitFourierCoefficient r f χ‖ ^ 2) =
      (r.totient : ℝ)⁻¹ * ∑ a : (ZMod r)ˣ, ‖f a‖ ^ 2 := by
  classical
  have hcomplex :
      (∑ χ : DirichletCharacter ℂ r,
        dirichletUnitFourierCoefficient r f χ *
          star (dirichletUnitFourierCoefficient r f χ)) =
        (r.totient : ℂ)⁻¹ * ∑ a : (ZMod r)ˣ, f a * star (f a) := by
    conv_lhs =>
      enter [2, χ, 1]
      unfold dirichletUnitFourierCoefficient
    simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.mul_sum]
    congr 1
    have hinv := congrArg star (dirichletUnitFourier_inversion r f a)
    simpa only [star_sum, star_mul, star_star, Finset.mul_sum, mul_assoc] using
      congrArg (fun z => f a * z) hinv
  have hnorm (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_pow, Complex.star_def] using Complex.mul_conj' z
  simp_rw [hnorm] at hcomplex
  have hcast : ((∑ χ : DirichletCharacter ℂ r,
      ‖dirichletUnitFourierCoefficient r f χ‖ ^ 2 : ℝ) : ℂ) =
      (((r.totient : ℝ)⁻¹ * ∑ a : (ZMod r)ˣ, ‖f a‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    simpa only [Complex.ofReal_pow] using hcomplex
  exact Complex.ofReal_injective hcast

theorem dirichletUnitFourier_l1_bound (f : (ZMod r)ˣ → ℂ)
    (hf : ∀ a, ‖f a‖ ≤ 1) :
    (∑ χ : DirichletCharacter ℂ r,
      ‖dirichletUnitFourierCoefficient r f χ‖) ≤ Real.sqrt (r.totient : ℝ) := by
  classical
  have hr : 0 < (r.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos r)
  have hmass : (∑ χ : DirichletCharacter ℂ r,
      ‖dirichletUnitFourierCoefficient r f χ‖ ^ 2) ≤ 1 := by
    rw [dirichletUnitFourier_parseval]
    calc
      _ ≤ (r.totient : ℝ)⁻¹ * ∑ _a : (ZMod r)ˣ, (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hr.le)
        apply Finset.sum_le_sum
        intro a _
        nlinarith [norm_nonneg (f a), hf a]
      _ = 1 := by simp [ZMod.card_units_eq_totient, hr.ne']
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (DirichletCharacter ℂ r)) (fun _ => (1 : ℝ))
    (fun χ => ‖dirichletUnitFourierCoefficient r f χ‖)
  have hcard : Fintype.card (DirichletCharacter ℂ r) = r.totient :=
    Nat.card_eq_fintype_card.symm.trans
      (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r)
  simpa only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul,
    mul_one, hcard, Real.sqrt_one] using
    hcs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmass)
      (Real.sqrt_nonneg _))

end
end ArtinMatthews
