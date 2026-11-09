module

public import ArtinMatthews.MarkedRootDiscrepancyAbsorption
public import ArtinMatthews.MarkedMinorArcProductMassActual


set_option backward.privateInPublic true
@[expose] public section

/-! The source grid exponent c/8 and the genuine growing-moment target.
The grid has a power number of cells, explicitly retained below. -/

noncomputable section
namespace ArtinMatthews
open Filter

def markedRootGridSize (c x : ℝ) : ℕ := ⌈x^(c/8)⌉₊

theorem markedRootGridSize_bounds {c x : ℝ} (hc : 0 < c) (hx : 1 ≤ x) :
    0 < markedRootGridSize c x ∧
      (markedRootGridSize c x : ℝ) ≤ 2*x^(c/8) ∧
      1/(markedRootGridSize c x : ℝ) ≤ x^(-c/8) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have ht : 0 < x^(c/8) := Real.rpow_pos_of_pos hx0 _
  have h1 : 1 ≤ x^(c/8) := Real.one_le_rpow hx (by positivity)
  have hlo : x^(c/8) ≤ (markedRootGridSize c x : ℝ) := Nat.le_ceil _
  have hhi := Nat.ceil_lt_add_one ht.le
  have hN : 0 < (markedRootGridSize c x : ℝ) := ht.trans_le hlo
  refine ⟨by exact_mod_cast hN,?_,?_⟩
  · change (⌈x^(c/8)⌉₊ : ℝ) ≤ _
    linarith
  · rw [show -c/8=-(c/8) by ring,Real.rpow_neg hx0.le,one_div]
    exact inv_anti₀ ht hlo

theorem markedRootGridSize_discrepancy {c x : ℝ} (hc : 0 < c) (hx : 1 ≤ x) :
    15*(markedRootGridSize c x : ℝ)^3*x^(-c) ≤ 120*x^(-5*c/8) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hb := (markedRootGridSize_bounds hc hx).2.1
  calc
    _ ≤ 15*(2*x^(c/8))^3*x^(-c) := by gcongr
    _ = 120*(x^(c/8))^3*x^(-c) := by ring
    _ = 120*x^(-5*c/8) := by
      rw [← Real.rpow_mul_natCast hx0.le,mul_assoc,← Real.rpow_add hx0]
      congr 2
      norm_num
      ring

theorem markedRoot_power_le_moment_log (b A : ℝ) (hb : 0 < b) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop,
      x^(-b) ≤ (Real.log x)^(-A*(markedMemoryMomentLength x : ℝ)) := by
  have hr : Tendsto (fun L : ℝ => (3*A)*(Real.log L/L^(1/2:ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero).const_mul (3*A)
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    Real.tendsto_log_atTop.eventually (hr.eventually (Iio_mem_nhds hb)),
    eventually_gt_atTop (0:ℝ)] with x hL hsmall hx
  let L := Real.log x
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hs : 0 < L^(1/2:ℝ) := Real.rpow_pos_of_pos hLp _
  have hs1 : 1 ≤ L^(1/2:ℝ) := Real.one_le_rpow hL (by norm_num)
  have hceil := Nat.ceil_lt_add_one (div_nonneg hs.le (by norm_num : (0:ℝ)≤2))
  have hN : (markedMemoryMomentLength x : ℝ) ≤ 3*L^(1/2:ℝ) := by
    unfold markedMemoryMomentLength
    change ((2*⌈L^(1/2:ℝ)/2⌉₊ : ℕ) : ℝ) ≤ _
    push_cast
    linarith
  have hratio : 3*A*Real.log L ≤ b*L^(1/2:ℝ) := by
    have hh : (3*A*Real.log L)/L^(1/2:ℝ) < b := by simpa only [div_eq_mul_inv,mul_assoc] using hsmall
    exact ((div_lt_iff₀ hs).mp hh).le
  have hsquare : L^(1/2:ℝ)*L^(1/2:ℝ) = L := by
    rw [← Real.rpow_add hLp]
    norm_num
  have hscale := mul_le_mul_of_nonneg_right hratio hs.le
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hexp : A*(markedMemoryMomentLength x : ℝ)*Real.log L ≤ b*L := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hA) hlog0
    rw [mul_assoc b,hsquare] at hscale
    nlinarith
  rw [Real.rpow_def_of_pos hx,Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  dsimp only [L] at hexp
  nlinarith

end ArtinMatthews
