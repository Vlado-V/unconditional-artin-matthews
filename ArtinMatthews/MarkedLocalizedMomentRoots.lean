module

public import ArtinMatthews.MarkedPositionLocalizedMoment
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! Taking the genuine 2R-th root of the localized moment inequality.
The cell-size factor is retained explicitly. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedPower_bound_root (z C : ℝ) (hz : 0≤z)
    (n : ℕ) (hn : n≠0) (h : z^n≤C) : z≤C^((n:ℝ)⁻¹) := by
  have hp := Real.rpow_le_rpow (pow_nonneg hz _) h (inv_nonneg.mpr (Nat.cast_nonneg n : (0:ℝ)≤n))
  rwa [Real.pow_rpow_inv_natCast hz hn] at hp

theorem markedMoment_root_factor (x : ℝ) (hx : 0≤x) (k : ℕ) :
    (x^(k+1))^((2*((k+1:ℕ):ℝ))⁻¹)=Real.sqrt x := by
  rw [← Real.rpow_natCast_mul hx,Real.sqrt_eq_rpow]
  congr 1
  have hk : ((k+1:ℕ):ℝ)≠0 := by positivity
  field_simp

theorem markedLocalizedMoment_root_bound
    (z B E F C T : ℝ) (hz : 0≤z) (hB : 0≤B) (hE : 0≤E) (hF : 0≤F)
    (hC : 0≤C) (hT : 0≤T) (k : ℕ)
    (h : z^(2*(k+1))≤B^(k+1)*E^(k+1)*F^k*C*T) :
    z≤Real.sqrt B*Real.sqrt E*F^((k:ℝ)/(2*((k+1:ℕ):ℝ))) *
      C^((2*((k+1:ℕ):ℝ))⁻¹)*T^((2*((k+1:ℕ):ℝ))⁻¹) := by
  have hp := markedPower_bound_root z _ hz (2*(k+1)) (by omega) h
  have he : ((2*(k+1):ℕ):ℝ)=2*((k+1:ℕ):ℝ) := by push_cast; rfl
  rw [he] at hp
  rw [Real.mul_rpow (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hB _) (pow_nonneg hE _))
      (pow_nonneg hF _)) hC) hT,
    Real.mul_rpow (mul_nonneg (mul_nonneg (pow_nonneg hB _) (pow_nonneg hE _)) (pow_nonneg hF _)) hC,
    Real.mul_rpow (mul_nonneg (pow_nonneg hB _) (pow_nonneg hE _)) (pow_nonneg hF _),
    Real.mul_rpow (pow_nonneg hB _) (pow_nonneg hE _),
    markedMoment_root_factor B hB k,markedMoment_root_factor E hE k,
    ← Real.rpow_natCast_mul hF] at hp
  simpa only [div_eq_mul_inv] using hp

end
end ArtinMatthews
