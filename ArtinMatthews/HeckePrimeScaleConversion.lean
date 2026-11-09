module

public import ArtinMatthews.HeckePrimeNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit removal of the square-root normalization and residue-degree
error in the actual rational prime estimate. -/

noncomputable section
namespace ArtinMatthews
open OAI.SevenEighths

theorem heckePrime_sqrt_floor_le {H : ℝ} (hH : 0 ≤ H) (b : ℝ) :
    (Nat.sqrt ⌊max 1 b*H⌋₊ : ℝ) ≤ max 1 b*H^(1/2 : ℝ) := by
  have hN : ((Nat.sqrt ⌊max 1 b*H⌋₊ : ℝ))^2 ≤ (⌊max 1 b*H⌋₊ : ℝ) := by
    exact_mod_cast Nat.sqrt_le' ⌊max 1 b*H⌋₊
  have hfloor : (⌊max 1 b*H⌋₊ : ℝ) ≤ max 1 b*H := Nat.floor_le (by positivity)
  have hsq : (H^(1/2 : ℝ))^2 = H := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hH]
    norm_num
  have hm : max 1 b ≤ (max 1 b)^2 := by nlinarith [le_max_left (1 : ℝ) b]
  have hbound : (max 1 b)*H ≤ (max 1 b)^2*H := mul_le_mul_of_nonneg_right hm hH
  have hpow : (max 1 b*H^(1/2 : ℝ))^2 = (max 1 b)^2*H := by rw [mul_pow, hsq]
  have hnonneg : 0 ≤ max 1 b*H^(1/2 : ℝ) := by positivity
  nlinarith

theorem heckeRationalPrimeSum_of_polynomial_power (η : HeckeFamily.Character)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (W : ℝ → ℂ)
    (b H t K BW : ℝ) (hH : 1 ≤ H) (hBW : 0 ≤ BW) (hW : ∀ y, ‖W y‖ ≤ BW)
    (hpoly : ‖HeckePrimeAnnular.primePolynomial (heckeDirichletTwist η χ) W b H 0 t‖ ≤
      K*H^(13/32 : ℝ)) :
    ‖heckeRationalPrimeSum η χ W ⌊max 1 b*H⌋₊ H t‖ ≤
      (K+3*max 1 b*BW)*H^(29/32 : ℝ) := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hcancel : H^(-(1/2 : ℝ))*H^(1/2 : ℝ) = 1 := by
    rw [← Real.rpow_add hHp]
    norm_num
  have herror : H^(-(1/2 : ℝ))*(3*(Nat.sqrt ⌊max 1 b*H⌋₊ : ℝ)*BW) ≤
      3*max 1 b*BW := by
    calc
      _ ≤ H^(-(1/2 : ℝ))*(3*(max 1 b*H^(1/2 : ℝ))*BW) := by
        gcongr
        exact heckePrime_sqrt_floor_le hHp.le b
      _ = (3*max 1 b*BW)*(H^(-(1/2 : ℝ))*H^(1/2 : ℝ)) := by ring
      _ = _ := by rw [hcancel, mul_one]
  have hh := (heckeRationalPrimeSum_le_primePolynomial η χ W b H t BW hHp hBW hW).trans
    (add_le_add hpoly herror)
  have hpow : 1 ≤ H^(13/32 : ℝ) := Real.one_le_rpow hH (by norm_num)
  have hsmall : 3*max 1 b*BW ≤ (3*max 1 b*BW)*H^(13/32 : ℝ) :=
    le_mul_of_one_le_right (by positivity) hpow
  have hh' := hh.trans (add_le_add le_rfl hsmall)
  have he := mul_le_mul_of_nonneg_left hh' (Real.rpow_nonneg hHp.le (1/2 : ℝ))
  have hleft : H^(1/2 : ℝ)*(H^(-(1/2 : ℝ))*
      ‖heckeRationalPrimeSum η χ W ⌊max 1 b*H⌋₊ H t‖) =
      ‖heckeRationalPrimeSum η χ W ⌊max 1 b*H⌋₊ H t‖ := by
    rw [← mul_assoc, mul_comm (H^(1/2 : ℝ)), hcancel, one_mul]
  rw [hleft] at he
  convert he using 1
  rw [← add_mul, mul_left_comm, ← Real.rpow_add hHp]
  norm_num

end ArtinMatthews
