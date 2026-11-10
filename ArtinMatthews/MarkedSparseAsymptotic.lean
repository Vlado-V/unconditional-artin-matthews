module

public import ArtinMatthews.MarkedMomentAmplification
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform numerical amplification for the prime scales in the marked
major-arc argument. The numerical optimization follows the proved sample-cost
argument in OpenAI math-main's `MRTExtraSampleScale`, with the exponent ranges
and fixed constants changed to those actually used here. -/

namespace ArtinMatthews

open Filter ReusedMoments

noncomputable def sparseMomentPrefactor (R D : ℝ) : ℝ :=
  24 * Real.exp 1 * (2 + (R * D)^2)

noncomputable def sparseMomentExponent (R A : ℝ) : ℝ :=
  R * (|Real.log (8 * R)| + 1 + 2 * A)

/-- A pointwise optimization with explicit, fixed numerical envelopes. -/
theorem marked_sparse_cost_pointwise {L Y T R D A : ℝ}
    (hL : 1 ≤ L) (hLL : 1 ≤ Real.log L)
    (hR : 0 < R) (hD : 0 < D) (hA : 0 ≤ A)
    (hY : 1 < Y) (hT : 1 < T)
    (hr : (mrtAmplificationOrder Y T : ℝ) ≤ R * L^(9/(10:ℝ)))
    (hlog4 : Real.log (4*Y) ≤ D * L)
    (hsmall : (|Real.log (sparseMomentPrefactor R D)| + 4 +
      sparseMomentExponent R A) * Real.log L ≤ L^(1/(100:ℝ))) :
    mrtShortPrimeSampleCost Y (L^(-A)) T (mrtAmplificationOrder Y T) ≤
      Real.exp (L^(91/(100:ℝ))) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hV : 0 < L^(-A) := Real.rpow_pos_of_pos hL0 _
  let r := mrtAmplificationOrder Y T
  have hrpos : 0 < r := by
    dsimp [r,mrtAmplificationOrder]
    exact Nat.ceil_pos.mpr (div_pos (Real.log_pos hT) (Real.log_pos hY))
  have hr0 : (0:ℝ) < r := by exact_mod_cast hrpos
  have hpow1 : 1 ≤ L^(9/(10:ℝ)) := Real.one_le_rpow hL (by norm_num)
  have hpowL : L^(9/(10:ℝ)) ≤ L := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (show (9/(10:ℝ)) ≤ 1 by norm_num)
  have hrL : (r:ℝ) ≤ R * L := hr.trans (mul_le_mul_of_nonneg_left hpowL hR.le)
  have hlog40 : 0 ≤ Real.log (4*Y) := Real.log_nonneg (by linarith)
  have hrl : 0 ≤ (r:ℝ)*Real.log (4*Y) := mul_nonneg hr0.le hlog40
  have hrlb : (r:ℝ)*Real.log (4*Y) ≤ (R*D)*L^2 := by
    calc
      _ ≤ (R*L)*(D*L) := mul_le_mul hrL hlog4 hlog40 (by positivity)
      _ = _ := by ring
  have hL4 : 1 ≤ L^4 := one_le_pow₀ hL
  have hpref : 24*Real.exp 1*(2+((r:ℝ)*Real.log (4*Y))^2) ≤
      sparseMomentPrefactor R D * L^4 := by
    have hs := pow_le_pow_left₀ hrl hrlb 2
    have he : ((R*D)*L^2)^2 = (R*D)^2 * L^4 := by ring
    rw [he] at hs
    have ht : 2+((r:ℝ)*Real.log (4*Y))^2 ≤ (2+(R*D)^2)*L^4 := by nlinarith
    calc
      _ ≤ 24*Real.exp 1*((2+(R*D)^2)*L^4) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by unfold sparseMomentPrefactor; ring
  have hlr : Real.log (8*(r:ℝ)) ≤ (|Real.log (8*R)|+1)*Real.log L := by
    have hh := Real.log_le_log (by positivity : 0 < 8*(r:ℝ))
      (mul_le_mul_of_nonneg_left hrL (by norm_num : (0:ℝ) ≤ 8))
    have he : (8:ℝ)*(R*L)=(8*R)*L := by ring
    rw [he,Real.log_mul (by positivity : (8*R) ≠ 0) hL0.ne'] at hh
    have hc : Real.log (8*R) ≤ |Real.log (8*R)| *Real.log L :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hLL)
    nlinarith
  have hlogV : Real.log (L^(-A)) = -A*Real.log L := Real.log_rpow hL0 _
  have hexp : (r:ℝ)*(Real.log (8*(r:ℝ))-2*Real.log (L^(-A))) ≤
      sparseMomentExponent R A * L^(9/(10:ℝ))*Real.log L := by
    rw [hlogV]
    calc
      _ ≤ (r:ℝ)*((|Real.log (8*R)|+1+2*A)*Real.log L) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hr0.le
      _ ≤ (R*L^(9/(10:ℝ)))*((|Real.log (8*R)|+1+2*A)*Real.log L) :=
        mul_le_mul_of_nonneg_right hr (by positivity)
      _ = _ := by unfold sparseMomentExponent; ring
  have hscalar : Real.log (sparseMomentPrefactor R D)+4*Real.log L+
      sparseMomentExponent R A*L^(9/(10:ℝ))*Real.log L ≤ L^(91/(100:ℝ)) := by
    have hbig : 1 ≤ L^(9/(10:ℝ))*Real.log L :=
      one_le_mul_of_one_le_of_one_le hpow1 hLL
    have hc : Real.log (sparseMomentPrefactor R D) ≤
        |Real.log (sparseMomentPrefactor R D)| * (L^(9/(10:ℝ))*Real.log L) :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hbig)
    have hlog : Real.log L ≤ L^(9/(10:ℝ))*Real.log L :=
      le_mul_of_one_le_left (by positivity) hpow1
    calc
      _ ≤ L^(9/(10:ℝ))*((|Real.log (sparseMomentPrefactor R D)| + 4 +
          sparseMomentExponent R A)*Real.log L) := by nlinarith
      _ ≤ L^(9/(10:ℝ))*L^(1/(100:ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hL0.le _)
      _ = _ := by rw [← Real.rpow_add hL0]; norm_num
  have he := mrt_short_prime_sample_cost_exp hY hV hT
  have hfour : Real.exp (4*Real.log L) = L^4 := by
    simpa only [Nat.cast_ofNat,Real.exp_log hL0] using
      Real.exp_nat_mul (Real.log L) 4
  change mrtShortPrimeSampleCost Y (L^(-A)) T r ≤ _ at he ⊢
  calc
    _ ≤ (sparseMomentPrefactor R D*L^4)*
        Real.exp (sparseMomentExponent R A*L^(9/(10:ℝ))*Real.log L) :=
      he.trans (mul_le_mul hpref (Real.exp_le_exp.mpr hexp) (by positivity)
        (by unfold sparseMomentPrefactor; positivity))
    _ = Real.exp (Real.log (sparseMomentPrefactor R D)+4*Real.log L+
        sparseMomentExponent R A*L^(9/(10:ℝ))*Real.log L) := by
      rw [Real.exp_add,Real.exp_add,
        Real.exp_log (by unfold sparseMomentPrefactor; positivity),hfour]
    _ ≤ _ := Real.exp_le_exp.mpr hscalar

/-- The explicit envelopes are absorbed uniformly; the eventual threshold
may depend on the fixed constants, but not on either scale. -/
theorem marked_sparse_cost_envelopes (R D A : ℝ)
    (hR : 0 < R) (hD : 0 < D) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ Y T : ℝ, 1 < Y → 1 < T →
      (mrtAmplificationOrder Y T : ℝ) ≤ R * L^(9/(10:ℝ)) →
      Real.log (4*Y) ≤ D * L →
      mrtShortPrimeSampleCost Y (L^(-A)) T (mrtAmplificationOrder Y T) ≤
        Real.exp (L^(91/(100:ℝ))) := by
  let C := |Real.log (sparseMomentPrefactor R D)| + 4 + sparseMomentExponent R A
  have hC : 0 < C := by dsimp [C,sparseMomentExponent]; positivity
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ) < 1/100 by norm_num)).bound
    (show 0 < 1/C by positivity)
  filter_upwards [hb,eventually_ge_atTop (1:ℝ),
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)))] with L hb hL hLL
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hlog0 : 0 ≤ Real.log L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg hlog0,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hb
  have hs : C*Real.log L ≤ L^(1/(100:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hb hC.le
    have he : C*((1/C)*L^(1/(100:ℝ)))=L^(1/(100:ℝ)) := by field_simp
    simpa only [he] using hh
  intro Y T hY hT hr hlog4
  exact marked_sparse_cost_pointwise hL hLL hR hD hA hY hT hr hlog4 hs

/-- The paper's full logarithmic prime-scale range gives the sparse moment
bound, uniformly for all admissible prime scales and frequency heights. -/
theorem marked_sparse_cost_log_scales (c C₁ C₂ A : ℝ)
    (hc : 0 < c) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ Y T : ℝ, 1 < Y →
      c * L^(1/(10:ℝ)) ≤ Real.log Y →
      Real.log Y ≤ C₁ * L^(1/(5:ℝ)) → 1 < T → Real.log T ≤ C₂ * L →
      mrtShortPrimeSampleCost Y (L^(-A)) T (mrtAmplificationOrder Y T) ≤
        Real.exp (L^(91/(100:ℝ))) := by
  let R := C₂/c + 1
  let D := C₁ + 3
  have hR : 0 < R := by dsimp [R]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  filter_upwards [marked_sparse_cost_envelopes R D A hR hD hA,
    eventually_ge_atTop (1:ℝ)] with L hcost hL
  intro Y T hY hlo hhi hT hTU
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpow1 : 1 ≤ L^(9/(10:ℝ)) := Real.one_le_rpow hL (by norm_num)
  have hratio : C₂ * L / (c * L^(1/(10:ℝ))) = (C₂/c) * L^(9/(10:ℝ)) := by
    apply (div_eq_iff (mul_pos hc (Real.rpow_pos_of_pos hL0 _)).ne').mpr
    rw [mul_assoc, mul_left_comm (L^(9/(10:ℝ))) c, ← mul_assoc,
      mul_assoc (C₂/c) c, ← Real.rpow_add hL0]
    norm_num
    field_simp
  have hr : (mrtAmplificationOrder Y T : ℝ) ≤ R * L^(9/(10:ℝ)) := by
    have hceil := (mrt_amplification_order_bounds hY hT.le).2.2.le
    calc
      _ ≤ Real.log T/Real.log Y+1 := hceil
      _ ≤ C₂ * L/(c * L^(1/(10:ℝ)))+1 := by
        have hd := (div_le_div_of_nonneg_right hTU (Real.log_pos hY).le).trans
          (div_le_div_of_nonneg_left (mul_nonneg hC₂.le hL0.le)
            (mul_pos hc (Real.rpow_pos_of_pos hL0 _)) hlo)
        linarith
      _ ≤ _ := by rw [hratio]; dsimp [R]; nlinarith
  have hpowL : L^(1/(5:ℝ)) ≤ L := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (show (1/(5:ℝ)) ≤ 1 by norm_num)
  have hlog4 : Real.log (4*Y) ≤ D * L := by
    rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by linarith : Y ≠ 0)]
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    have hh := hhi.trans (mul_le_mul_of_nonneg_left hpowL hC₁.le)
    dsimp [D]
    nlinarith
  exact hcost Y T hY hT hr hlog4

end ArtinMatthews
