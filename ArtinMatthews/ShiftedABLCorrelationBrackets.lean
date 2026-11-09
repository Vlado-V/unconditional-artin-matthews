module

public import ArtinMatthews.ShiftedABLPositiveBracketBounds


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed circle power controls the two declining contributions.
The remaining two terms are the literal source correlation weights. -/

noncomputable section
namespace ArtinMatthews

private theorem nested_sqrt_le_self {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt (Real.sqrt x) ≤ x :=
  (Real.sqrt_le_self_iff.mpr (Or.inr (Real.one_le_sqrt.mpr hx))).trans
    (Real.sqrt_le_self_iff.mpr (Or.inr hx))

theorem shiftedABL_correlation_bracket_bound
    {H M N D d F r n R Q g P ε : ℝ}
    (hH : 1 ≤ H) (hM : 1 ≤ M) (hN : 1 ≤ N) (hd : 1 ≤ d) (hD : d ≤ D)
    (hF1 : 1 ≤ F) (hr1 : 1 ≤ r) (hn : 0 < n) (hR : 1 ≤ R) (hg : 1 ≤ g)
    (hP : 2 ≤ P) (hε : 0 ≤ ε) (hQ : P^36 ≤ Q)
    (hHP : H ≤ P) (hFup : F ≤ P^5) (hrup : r ≤ P^5) (hgup : g ≤ P^2)
    (hF : F=N*D^2) (hRup : R ≤ 64*(M/d)*P^ε*Q^2/H)
    (hgD : g ≤ N*D/d) (hrlow : (M/d)^2 ≤ r) :
    let X := Real.sqrt (R*n)/(Real.sqrt r*Q)
    let G := Real.sqrt (n*g)
    H*F*Real.sqrt r/Q * Real.sqrt (1+R/(r*F)) * Real.sqrt (1+G/(X*r*F)) ≤
      10*N*P^ε*(Real.sqrt (H+1)*Real.sqrt M*D/Real.sqrt d+
        (H+1)^(3/4 : ℝ)*D^(1/4 : ℝ)/M^(1/4 : ℝ)) := by
  intro X G
  let A := Real.sqrt (H+1)*Real.sqrt M*D/Real.sqrt d
  let B := (H+1)^(3/4 : ℝ)*D^(1/4 : ℝ)/M^(1/4 : ℝ)
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hD0 : 0 < D := hd0.trans_le hD
  have hF0 : 0 < F := zero_lt_one.trans_le hF1
  have hr0 : 0 < r := zero_lt_one.trans_le hr1
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hP1 : 1 ≤ P := by linarith
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := (pow_pos hP0 36).trans_le hQ
  have hW : 1 ≤ P^ε := Real.one_le_rpow hP1 hε
  have hA1 : 1 ≤ A := by
    have hds : Real.sqrt d ≤ D := (Real.sqrt_le_self_iff.mpr (Or.inr hd)).trans hD
    have hA' := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (Real.one_le_sqrt.mpr (show 1 ≤ H+1 by linarith)) (Real.one_le_sqrt.mpr hM))
      ((one_le_div (Real.sqrt_pos.mpr hd0)).mpr hds)
    exact hA'.trans_eq (by dsimp [A]; ring)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hmain1 : 1 ≤ A+B := hA1.trans (le_add_of_nonneg_right hB0)
  have hWmain : 1 ≤ P^ε*(A+B) := one_le_mul_of_one_le_of_one_le hW hmain1
  have hNmain : 1 ≤ N*(P^ε*(A+B)) := one_le_mul_of_one_le_of_one_le hN hWmain
  have hsr : Real.sqrt r ≤ P^5 := (Real.sqrt_le_self_iff.mpr (Or.inr hr1)).trans hrup
  have hsf : Real.sqrt F ≤ P^5 := (Real.sqrt_le_self_iff.mpr (Or.inr hF1)).trans hFup
  have hqg : Real.sqrt (Real.sqrt g) ≤ P^2 := (nested_sqrt_le_self hg).trans hgup
  have hqr : Real.sqrt (Real.sqrt r) ≤ P^5 := (nested_sqrt_le_self hr1).trans hrup
  have hqR : 1 ≤ Real.sqrt (Real.sqrt R) := Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hR)
  have hQ11 : P^11 ≤ Q := (pow_le_pow_right₀ hP1 (by decide : (11 : ℕ) ≤ 36)).trans hQ
  have hQsqrt : P^18 ≤ Real.sqrt Q := Real.le_sqrt_of_sq_le (by
    calc (P^18)^2 = P^36 := by ring
         _ ≤ Q := hQ)
  have hQ13 : P^13 ≤ Real.sqrt Q :=
    (pow_le_pow_right₀ hP1 (by decide : (13 : ℕ) ≤ 18)).trans hQsqrt
  have hdecay0 : H*F*Real.sqrt r/Q ≤ 1 := by
    calc
      _ ≤ P*P^5*P^5/Q := by gcongr
      _ = P^11/Q := by ring
      _ ≤ 1 := (div_le_one hQ0).mpr hQ11
  have hdecay1 : H*Real.sqrt F*Real.sqrt (Real.sqrt g)*Real.sqrt (Real.sqrt r)/
      (Real.sqrt Q*Real.sqrt (Real.sqrt R)) ≤ 1 := by
    have hden : Real.sqrt Q ≤ Real.sqrt Q*Real.sqrt (Real.sqrt R) :=
      le_mul_of_one_le_right (Real.sqrt_nonneg _) hqR
    calc
      _ ≤ (P*P^5*P^2*P^5)/(Real.sqrt Q*Real.sqrt (Real.sqrt R)) := by gcongr
      _ ≤ (P*P^5*P^2*P^5)/Real.sqrt Q :=
        div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hQ0) hden
      _ = P^13/Real.sqrt Q := by ring
      _ ≤ 1 := (div_le_one (Real.sqrt_pos.mpr hQ0)).mpr hQ13
  have hfirst : H*Real.sqrt F*Real.sqrt R/Q ≤ 8*N*P^ε*A :=
    shiftedABL_first_positive_bracket hH0 hM0 hN hD0.le hd0 hR0.le hQ0 hP1 hε hF hRup
  have hsecond : H*Real.sqrt (Real.sqrt g)*Real.sqrt (Real.sqrt R)/
      (Real.sqrt Q*Real.sqrt (Real.sqrt r)) ≤ 4*N*P^ε*B :=
    shiftedABL_second_positive_bracket hH0 hM0 hN hD0 hd0 hr0 hR0.le hQ0
      hP1 hε (zero_le_one.trans hg) hRup hgD hrlow
  calc
    _ ≤ _ := shiftedABL_spectral_brackets_expand hH0.le hF0 hr0 hn hR0 hQ0 (zero_le_one.trans hg)
    _ ≤ 1+(8*N*P^ε*A)+1+(4*N*P^ε*B) := add_le_add
      (add_le_add (add_le_add hdecay0 hfirst) hdecay1) hsecond
    _ ≤ 2+8*N*P^ε*(A+B) := by
      nlinarith only [mul_nonneg (mul_nonneg (zero_le_one.trans hN) (zero_le_one.trans hW)) hB0]
    _ ≤ 10*N*P^ε*(A+B) := by nlinarith only [hNmain]

end ArtinMatthews
