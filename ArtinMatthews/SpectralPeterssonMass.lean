module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The exact real Gamma mass and its cancellation in the normalized Gram. -/

noncomputable section
open MeasureTheory Set

namespace ArtinMatthews

def spectralPeterssonReproducingMass (k : ℕ) (n : ℕ+) : ℝ :=
  Real.Gamma ((k-1 : ℕ) : ℝ)/(4*Real.pi*(n : ℝ))^(k-1)

theorem spectralPeterssonReproducingMass_pos (k : ℕ) (hk : 2 ≤ k) (n : ℕ+) :
    0 < spectralPeterssonReproducingMass k n := by
  unfold spectralPeterssonReproducingMass
  exact div_pos (Real.Gamma_pos_of_pos (Nat.cast_pos.mpr (by omega))) (by positivity)

theorem spectralPeterssonReproducingMass_integral (k : ℕ) (hk : 2 ≤ k) (n : ℕ+) :
    (∫ y in Ioi (0 : ℝ), y^(k-2)*Real.exp (-(4*Real.pi*(n : ℝ)*y))) =
      spectralPeterssonReproducingMass k n := by
  let r := 4*Real.pi*(n : ℝ)
  have ha : 0 < ((k-1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hr : 0 < r := by positivity
  have he : ((k-1 : ℕ) : ℝ)-1 = ((k-2 : ℕ) : ℝ) := by
    have hNat : (k-2)+1 = k-1 := by omega
    have hReal : ((k-2 : ℕ) : ℝ)+1 = ((k-1 : ℕ) : ℝ) := by exact_mod_cast hNat
    linarith
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
  rw [he] at h
  simp only [Real.rpow_natCast] at h
  change _ = Real.Gamma ((k-1 : ℕ) : ℝ)/r^(k-1)
  rw [h,one_div,inv_pow,div_eq_mul_inv,mul_comm]

def spectralPeterssonNormalization (k : ℕ) (n : ℕ+) : ℝ :=
  (Real.sqrt (spectralPeterssonReproducingMass k n))⁻¹

theorem spectralPeterssonReproducingMass_ratio (k : ℕ) (m n : ℕ+) :
    spectralPeterssonReproducingMass k n * ((n : ℝ)/(m : ℝ))^(k-1) =
      spectralPeterssonReproducingMass k m := by
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr m.property
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr n.property
  have hπ : 0 < 4*Real.pi := by positivity
  unfold spectralPeterssonReproducingMass
  simp only [div_pow,mul_pow]
  field_simp [hπ.ne',hm.ne',hn.ne']

theorem spectralPeterssonNormalization_mass (k : ℕ) (hk : 2 ≤ k) (m n : ℕ+) :
    (spectralPeterssonNormalization k n*spectralPeterssonNormalization k m)*
      spectralPeterssonReproducingMass k n =
        Real.sqrt (spectralPeterssonReproducingMass k n)/Real.sqrt (spectralPeterssonReproducingMass k m) := by
  have hn := spectralPeterssonReproducingMass_pos k hk n
  have hm := spectralPeterssonReproducingMass_pos k hk m
  unfold spectralPeterssonNormalization
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hn),ne_of_gt (Real.sqrt_pos.mpr hm)]
  exact (Real.sq_sqrt hn.le).symm

theorem spectralPeterssonNormalization_ratio (k : ℕ) (hk : 2 ≤ k) (m n : ℕ+) :
    (Real.sqrt (spectralPeterssonReproducingMass k n)/Real.sqrt (spectralPeterssonReproducingMass k m))*
      Real.sqrt ((n : ℝ)/(m : ℝ))^(k-1) = 1 := by
  have hm := spectralPeterssonReproducingMass_pos k hk m
  have hn := spectralPeterssonReproducingMass_pos k hk n
  have hmn : 0 ≤ (n : ℝ)/(m : ℝ) := by positivity
  let a := Real.sqrt (spectralPeterssonReproducingMass k n)
  let b := Real.sqrt (spectralPeterssonReproducingMass k m)
  let d := Real.sqrt ((n : ℝ)/(m : ℝ))
  have hs : (a*d^(k-1))^2 = b^2 := by
    have hd : (d^(k-1))^2 = ((n : ℝ)/(m : ℝ))^(k-1) := by
      rw [pow_right_comm d,Real.sq_sqrt hmn]
    rw [mul_pow,hd,Real.sq_sqrt hn.le,Real.sq_sqrt hm.le,spectralPeterssonReproducingMass_ratio]
  have he : a*d^(k-1) = b := le_antisymm (le_of_sq_le_sq hs.le (by dsimp only [b]; positivity))
    (le_of_sq_le_sq hs.ge (by dsimp only [a,d]; positivity))
  change (a/b)*d^(k-1) = 1
  rw [div_mul_eq_mul_div,he,div_self (ne_of_gt (Real.sqrt_pos.mpr hm))]

end ArtinMatthews
