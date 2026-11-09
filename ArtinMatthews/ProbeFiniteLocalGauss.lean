module

public import ArtinMatthews.VaryingKummerAnalyticIdealGaussFourier
public import OAI.NumberTheory.DirichletL.Detector.Gauss
public import Mathlib.FieldTheory.Finite.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The residue-field Gauss factors in source05.  Exponent zero means the
principal multiplicative character, still extended by zero at zero.  The
absent modulus is a separate one-point factor, not that character. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [Field F] [Fintype F]

def probeResidueGauss (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (v : ℕ) (y : F) : ℂ :=
  ∑ x : F, (χ ^ v) x * ψ (y * x)

def probeAbsentModulusFactor : ℂ := 1

omit [Fintype F] in
theorem probeResidueGauss_mask_at_zero (χ : MulChar F ℂ) (v : ℕ) :
    (χ ^ v) 0 = 0 := MulChar.map_zero _

omit [Fintype F] in
theorem probeAbsentModulusFactor_ne_mask (χ : MulChar F ℂ) :
    probeAbsentModulusFactor ≠ (χ ^ 0) 0 := by
  rw [probeAbsentModulusFactor, probeResidueGauss_mask_at_zero]
  exact one_ne_zero

theorem probeResidueGauss_nonzero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (v : ℕ) {y : F} (hy : y ≠ 0) :
    probeResidueGauss χ ψ v y = (χ ^ v)⁻¹ y * gaussSum (χ ^ v) ψ :=
  ProbeGauss.frequencyGauss_nonzero (χ ^ v) ψ hy

theorem probeResidueGauss_zero_nonprincipal (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (v : ℕ) (hv : χ ^ v ≠ 1) :
    probeResidueGauss χ ψ v 0 = 0 :=
  ProbeGauss.frequencyGauss_zero_nonprincipal (χ ^ v) ψ hv

theorem probeResidueGauss_principal (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (v : ℕ) (hv : χ ^ v = 1) (y : F) :
    probeResidueGauss χ ψ v y =
      if y = 0 then (Fintype.card F : ℂ) - 1 else -1 := by
  change ProbeGauss.frequencyGauss (χ ^ v) ψ y = _
  rw [hv, ProbeGauss.frequencyGauss_principal ψ hψ]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_units,
    Nat.cast_sub (Nat.succ_le_iff.mpr (Fintype.card_pos (α := F)))]
  norm_num

theorem probeResidueGauss_sixth (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (v : ℕ) (y : F) :
    probeResidueGauss χ ψ v y =
      if y = 0 then (if 6 ∣ v then (Fintype.card F : ℂ) - 1 else 0)
      else (χ ^ v)⁻¹ y * gaussSum (χ ^ v) ψ := by
  have hv : χ ^ v = 1 ↔ 6 ∣ v := by
    rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  by_cases hy : y = 0
  · subst y
    rw [ite_eq_left rfl]
    by_cases hd : 6 ∣ v
    · rw [ite_eq_left hd, probeResidueGauss_principal χ ψ hψ v (hv.mpr hd),
        ite_eq_left rfl]
    · rw [ite_eq_right hd, probeResidueGauss_zero_nonprincipal χ ψ v
        (fun h => hd (hv.mp h))]
  · rw [ite_eq_right hy, probeResidueGauss_nonzero χ ψ v hy]

theorem probeResidueGauss_period_six (χ : MulChar F ℂ) (hχ : χ ^ 6 = 1)
    (ψ : AddChar F ℂ) (v : ℕ) (y : F) :
    probeResidueGauss χ ψ (v + 6) y = probeResidueGauss χ ψ v y := by
  simp only [probeResidueGauss, pow_add, hχ, mul_one]

theorem probeResidueGauss_tau_principal (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    probeResidueGauss χ ψ 0 1 = -1 := by
  rw [probeResidueGauss_principal χ ψ hψ 0 (pow_zero χ), ite_eq_right one_ne_zero]

theorem probeResidueGauss_tau_norm (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (v : ℕ) (hv : χ ^ v ≠ 1) :
    ‖probeResidueGauss χ ψ v 1‖ = Real.sqrt (Fintype.card F : ℝ) := by
  simpa only [probeResidueGauss, one_mul, gaussSum] using
    primitive_gaussSum_norm (χ ^ v) (primitiveOnIdeals_of_field _ hv) ψ hψ

theorem probeResidueGauss_convolution (χ ξ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (y : F) :
    (∑ d : F, χ d * (∑ v : F, ξ v * ψ ((y - d) * v))) =
      χ⁻¹ (-1) * gaussSum χ ψ *
        (∑ v : F, (ξ * χ⁻¹) v * ψ (y * v)) :=
  ProbeGauss.finite_gauss_convolution χ ξ ψ y

theorem probeResidueGauss_convolution_even (χ ξ : MulChar F ℂ)
    (hχ : χ (-1) = 1) (ψ : AddChar F ℂ) (y : F) :
    (∑ d : F, χ d * (∑ v : F, ξ v * ψ ((y - d) * v))) =
      gaussSum χ ψ * (∑ v : F, (ξ * χ⁻¹) v * ψ (y * v)) := by
  rw [probeResidueGauss_convolution, MulChar.inv_apply_eq_inv', hχ, inv_one, one_mul]

theorem probeResidueGauss_power_convolution (χ : MulChar F ℂ)
    (hχ : χ (-1) = 1) (ψ : AddChar F ℂ) (t : ℕ) (y : F) :
    (∑ d : F, χ d * probeResidueGauss χ ψ (t + 1) (y - d)) =
      gaussSum χ ψ * probeResidueGauss χ ψ t y := by
  unfold probeResidueGauss
  rw [probeResidueGauss_convolution_even χ (χ ^ (t + 1)) hχ ψ]
  rw [pow_succ, mul_inv_cancel_right]

end

end ArtinMatthews.VaryingKummerAnalytic
