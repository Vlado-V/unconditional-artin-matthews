module

public import ArtinMatthews.GiantSignedTiltDensity
public import Mathlib.Algebra.Order.Ring.Pow


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative product-density errors retain the number of fresh slots. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedTilt_inverse_pow_error (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (n : ℕ) (hsmall : (n : ℝ) * δ ≤ 1 / 2) :
    ((1 - δ)⁻¹) ^ n - 1 ≤ 2 * (n : ℝ) * δ := by
  have hd : 0 ≤ (n : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ by linarith) n
  have hx : 1 - (n : ℝ) * δ ≤ (1 - δ) ^ n := by
    simpa only [mul_neg, sub_eq_add_neg] using hb
  have hxhalf : (1 : ℝ) / 2 ≤ (1 - δ) ^ n := by linarith
  have hxpos : 0 < (1 - δ) ^ n := by linarith
  have hprod := mul_nonneg hd (sub_nonneg.mpr hxhalf)
  rw [inv_pow, sub_le_iff_le_add]
  rw [← one_div]
  apply (div_le_iff₀ hxpos).mpr
  nlinarith

theorem idealFreshTargetMass_deficit_error
    {J : Type*} [Fintype J] {P : J → Finset ℕ} {k ell : ℕ}
    (r : ∀ j, P j → ℝ) (hr : ∀ j p, 0 ≤ r j p)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hupper : ∀ j p, r j p ≤ (1 - δ)⁻¹)
    (C : J → Finset (Fin k))
    (hsmall : ((∑ j, ((C j).card + ell) : ℕ) : ℝ) * δ ≤ 1 / 2)
    (a : MarkedPhysicalMarking P (k+ell)) :
    idealFreshTargetMass r C a - 1 ≤
      2 * ((∑ j, ((C j).card + ell) : ℕ) : ℝ) * δ := by
  have hmass := idealFreshTargetMass_upper r hr ((1 - δ)⁻¹) hupper C a
  rw [Finset.prod_pow_eq_pow_sum] at hmass
  exact (sub_le_sub_right hmass 1).trans
    (giantSignedTilt_inverse_pow_error δ hδ hδ1 _ hsmall)

theorem giantSignedActiveMass_deficit_error
    {J : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (r : ∀ j, P j → ℝ) (hr : ∀ j p, 0 ≤ r j p)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hupper : ∀ j p, r j p ≤ (1 - δ)⁻¹)
    (hsmall : ((Fintype.card J * M : ℕ) : ℝ) * δ ≤ 1 / 2)
    (a : MarkedPhysicalMarking P M) :
    giantSignedActiveMass r a - 1 ≤ 2 * ((Fintype.card J * M : ℕ) : ℝ) * δ :=
  (sub_le_sub_right (giantSignedActiveMass_upper r hr ((1 - δ)⁻¹) hupper a) 1).trans
    (giantSignedTilt_inverse_pow_error δ hδ hδ1 _ hsmall)

end
end ArtinMatthews
