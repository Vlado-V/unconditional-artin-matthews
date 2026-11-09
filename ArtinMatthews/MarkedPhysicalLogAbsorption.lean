module

public import ArtinMatthews.MarkedRootDiscrepancyAbsorption


set_option backward.privateInPublic true
@[expose] public section

/-! Final numerical absorption of two endpoint logarithmic weights,
the major-arc logarithmic factor and a genuine power-saving error. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped Asymptotics

theorem markedPhysicalGoodRemoval_budget
    (K C E G S A₀ b : ℝ) (hK : 0 ≤ K) (_hC : 0 ≤ C) (hE : 0 ≤ E) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop,
      K*((Real.log x)^S)^2 *
        (C*((Real.log x)^A₀)^3*(Real.log x)^(-(G+2*S+3*A₀+1)) + E*x^(-b)) ≤
          (Real.log x)^(-G) := by
  have hsmall := ((marked_root_power_isLittleO_log hb (G+2*S)).const_mul_left (K*E)).bound
    (by norm_num : (0 : ℝ)<1/2)
  filter_upwards [hsmall,eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2*K*C))] with x hx hx1 hlog
  let L := Real.log x
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hL : 0 < L := Real.log_pos hx1
  have hS : (L^S)^2 = L^(2*S) := by
    simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hL.le S 2).symm
  have hA : (L^A₀)^3 = L^(3*A₀) := by
    simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hL.le A₀ 3).symm
  have hsp : 0 ≤ (K*E)*x^(-b) := by positivity
  change ‖(K*E)*x^(-b)‖ ≤ (1/2 : ℝ)*‖L^(-(G+2*S))‖ at hx
  have htail : (K*E)*x^(-b) ≤ (1/2 : ℝ)*L^(-(G+2*S)) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hsp,
      abs_of_pos (Real.rpow_pos_of_pos hL (-(G+2*S)))] using hx
  have hpow : L^(-G-1)*L = L^(-G) := by
    calc
      _ = L^(-G-1)*L^(1 : ℝ) := by rw [Real.rpow_one]
      _ = L^((-G-1)+1) := (Real.rpow_add hL _ _).symm
      _ = _ := by congr 1; ring
  have hmain : K*C*L^(-G-1) ≤ (1/2 : ℝ)*L^(-G) := by
    apply (mul_le_mul_iff_right₀ hL).mp
    calc
      _ = (K*C)*(L^(-G-1)*L) := by ring
      _ = K*C*L^(-G) := by rw [hpow]
      _ ≤ ((1/2 : ℝ)*L)*L^(-G) := mul_le_mul_of_nonneg_right
        (by dsimp [L]; linarith) (Real.rpow_nonneg hL.le _)
      _ = _ := by ring
  have hmain_eq : K*(L^S)^2*(C*(L^A₀)^3*L^(-(G+2*S+3*A₀+1))) = K*C*L^(-G-1) := by
    rw [hS,hA]
    calc
      _ = (K*C)*(L^(2*S)*L^(3*A₀)*L^(-(G+2*S+3*A₀+1))) := by ring
      _ = _ := by rw [← Real.rpow_add hL,← Real.rpow_add hL]; congr 2; ring
  have htail_le : K*(L^S)^2*(E*x^(-b)) ≤ (1/2 : ℝ)*L^(-G) := by
    rw [hS]
    calc
      _ = L^(2*S)*((K*E)*x^(-b)) := by ring
      _ ≤ L^(2*S)*((1/2 : ℝ)*L^(-(G+2*S))) :=
        mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg hL.le _)
      _ = _ := by
        rw [mul_left_comm,← Real.rpow_add hL]
        congr 2
        ring
  change K*(L^S)^2*(C*(L^A₀)^3*L^(-(G+2*S+3*A₀+1)) + E*x^(-b)) ≤ L^(-G)
  rw [mul_add,hmain_eq]
  exact (add_le_add hmain htail_le).trans_eq (by ring)

end ArtinMatthews
