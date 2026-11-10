module

public import ArtinMatthews.GiantSlotCutoffCore
public import ArtinMatthews.GiantCofactorReciprocalMoment
public import ArtinMatthews.MarkedRoughCharacterRange
public import ArtinMatthews.PrimeExtractionLogMomentDecay
public import ArtinMatthews.PrimeExtractionWeightBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual mixed-cofactor truncation and cutoff shift on the
original hyperbola. The logarithmic cutoff is fixed by the tuple length. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped BigOperators Asymptotics Topology ContDiff

def giantOrdinaryTruncatedCofactor {k : ℕ} (i : Fin (k+1)) (γ x : ℝ) : ℕ → ℂ :=
  giantCofactorTruncate ((Real.log x)^(k*k+6))
    (giantMixedCofactorCoefficient i (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ))

def giantOrdinarySlotUnshifted {J : Type*} [Fintype J]
    (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ : ℝ) {k : ℕ} (i : Fin (k+1)) (x : ℝ) : ℂ :=
  giantSlotCutoffSum ⌊T*x⌋₊
    (giantOrdinarySlotCore e χ G x γ (giantOrdinaryTruncatedCofactor i γ x))
    (fun n => (Φ ((n:ℝ)/x):ℂ))

theorem giantOrdinaryTruncatedCofactor_bounds_eventually {k : ℕ}
    (hk : 0 < k) (i : Fin (k+1)) (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop,
      (∀ n,‖giantOrdinaryTruncatedCofactor i γ x n‖ ≤ (Real.log x)^(k*k+6)) ∧
      (∀ n,giantOrdinaryTruncatedCofactor i γ x n≠0 →
        x^γ < (n:ℝ) ∧ MarkedRoughAbove (Real.exp ((Real.log x)^(6/25:ℝ))) n) := by
  filter_upwards [marked_rough_log_cutoff_le_power (6/25) γ (by norm_num) hγ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0:ℝ))] with x hW hL
  exact ⟨fun n => giantCofactorTruncate_norm_le (pow_nonneg hL _) _ n,
    fun n hn => giantMixedCofactorCoefficient_support hk i hW (giantCofactorTruncate_ne_zero hn)⟩

private theorem giant_slot_log_cap_eventually (T : ℝ) (hT : 0 ≤ T) :
    ∀ᶠ x : ℝ in atTop,1+Real.log (⌊T*x⌋₊:ℝ) ≤ 3*Real.log x := by
  filter_upwards [eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (Real.log (T+1))))] with x hx hlog
  let X := ⌊T*x⌋₊
  have hL₁ : 1 ≤ Real.log x := (le_max_left _ _).trans hlog
  have hLT : Real.log (T+1) ≤ Real.log x := (le_max_right _ _).trans hlog
  change 1+Real.log (X:ℝ) ≤ _
  by_cases hX : X=0
  · rw [hX,Nat.cast_zero,Real.log_zero,add_zero]
    linarith
  · have hXp : 0 < (X:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hX)
    have hx₀ : 0 < x := zero_lt_one.trans_le hx
    have hXx : (X:ℝ) ≤ (T+1)*x := (Nat.floor_le (mul_nonneg hT hx₀.le)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hx₀.le)
    have h := Real.log_le_log hXp hXx
    rw [Real.log_mul (by positivity : (T+1)≠0) hx₀.ne'] at h
    linarith

private theorem giant_log_nat_power_isLittleO_x_div_log (d : ℕ) :
    (fun x : ℝ => (Real.log x)^d) =o[atTop] (fun x : ℝ => x/Real.log x) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact fun h => (div_pos (zero_lt_one.trans hx) (Real.log_pos hx)).ne' h |>.elim
  · have h := (isLittleO_log_rpow_rpow_atTop ((d+1:ℕ):ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero
    simp only [Real.rpow_natCast,Real.rpow_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    change (Real.log x)^(d+1)/x = (Real.log x)^d/(x/Real.log x)
    rw [pow_succ,div_div_eq_mul_div]

theorem giant_ordinary_slot_cutoff_error_isLittleO {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j,0 < e j) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (hG : ∀ᶠ x : ℝ in atTop,∀ n,‖G x n‖≤1)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ)
    (T γ : ℝ) (hT : 0 ≤ T) (hγ : 0 < γ) {k : ℕ} (i : Fin (k+1)) :
    (fun x => giantOrdinarySlotDiscrepancy e χ G Φ T γ i x -
      giantOrdinarySlotUnshifted e χ G Φ T γ i x) =o[atTop] (fun x : ℝ => x/Real.log x) := by
  let C := k*k+6
  let V := (2/Real.log 2)^(Fintype.card J)
  let F (x : ℝ) := giantOrdinarySlotDiscrepancy e χ G Φ T γ i x
  let U (x : ℝ) := giantOrdinarySlotUnshifted e χ G Φ T γ i x
  let B (x : ℝ) := giantSlotCutoffSum ⌊T*x⌋₊
    (giantOrdinarySlotCore e χ G x γ (giantOrdinaryTruncatedCofactor i γ x))
    (fun n => (Φ (((n-1:ℕ):ℝ)/x):ℂ))
  obtain ⟨D,hD,hweight⟩ := markedExtractionWeight_bound e he G zero_le_one hG Φ hΦ.continuous hT
  have hTailO : (fun x => F x-B x) =O[atTop] (fun x : ℝ => x*(Real.log x)^2/(Real.log x)^6) := by
    apply Asymptotics.IsBigO.of_bound (D*T*(3:ℝ)^(k*k))
    filter_upwards [hweight,giant_rough_slot_norm_le_one_eventually γ hγ,
      giant_centered_slot_norm_bound_eventually γ hγ,giant_slot_log_cap_eventually T hT,
      eventually_gt_atTop (1:ℝ)] with x hw hp hα hlog hx
    let L := Real.log x
    let X := ⌊T*x⌋₊
    let W := Real.exp (L^(6/25:ℝ))
    let β := giantMixedCofactorCoefficient i W (x^γ)
    have hx₀ : 0 < x := zero_lt_one.trans hx
    have hL : 0 < L := Real.log_pos hx
    have hX : (X:ℝ) ≤ T*x := Nat.floor_le (mul_nonneg hT hx₀.le)
    have hR : 0 < L^C := pow_pos hL _
    have htail := giant_mixed_cofactor_tail_le i W (x^γ) X hR (giant_prime_slot_norm_le_one _) hp
    have hleft := giantSlotCutoff_cofactor_difference e χ G Φ x γ X β
      (giantOrdinaryTruncatedCofactor i γ x) hD (sq_nonneg L)
      (fun v hv => hw v ((Nat.cast_le.mpr hv).trans hX)) hα
    change ‖F x-B x‖ ≤ _ * ‖x*L^2/L^6‖
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ x*L^2/L^6)]
    calc
      _ ≤ (D*L^2)*(X:ℝ)*((1+Real.log (X:ℝ))^(k*k)/L^C) := by
        dsimp only [F]
        rw [giantOrdinarySlotDiscrepancy_eq_cutoffSum]
        exact hleft.trans (mul_le_mul_of_nonneg_left htail (by positivity))
      _ ≤ (D*L^2)*(T*x)*((3*L)^(k*k)/L^C) := by
        gcongr
      _ = _ := by
        dsimp only [C]
        rw [mul_pow,pow_add L (k*k) 6]
        field_simp [hL.ne']
  have hTail : (fun x => F x-B x) =o[atTop] (fun x : ℝ => x/Real.log x) :=
    hTailO.trans_isLittleO (by simpa only [Real.rpow_neg_one,div_eq_mul_inv] using
      prime_extraction_log_moment_decay 1 (k:=6) (by norm_num))
  obtain ⟨K,hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hΦc hΦ (by simp)
  have hShiftO : (fun x => B x-U x) =O[atTop] (fun x : ℝ => (Real.log x)^(C+3)) := by
    apply Asymptotics.IsBigO.of_bound (3*T*V*(K:ℝ))
    filter_upwards [literalMarkedArrayWeight_bound_eventually e he,hG,
      giant_centered_slot_norm_bound_eventually γ hγ,giant_slot_log_cap_eventually T hT,
      eventually_gt_atTop (1:ℝ)] with x hV hGx hα hlog hx
    let L := Real.log x
    let X := ⌊T*x⌋₊
    let β := giantOrdinaryTruncatedCofactor i γ x
    have hx₀ : 0 < x := zero_lt_one.trans hx
    have hL : 0 < L := Real.log_pos hx
    have hX : (X:ℝ) ≤ T*x := Nat.floor_le (mul_nonneg hT hx₀.le)
    have hD₀ : 0 ≤ L^2*L^C*V := by dsimp only [V]; positivity
    have hA (m n : ℕ) : ‖giantOrdinarySlotCore e χ G x γ β m n‖ ≤ L^2*L^C*V := by
      have hb : ‖β n‖ ≤ L^C := giantCofactorTruncate_norm_le (pow_nonneg hL.le _) _ n
      simpa only [mul_one] using giantOrdinarySlotCore_norm_le e χ G x γ β m n
        (hα m) hb (hV _) (hGx _)
    change ‖B x-U x‖ ≤ _ * ‖L^(C+3)‖
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hL.le _)]
    calc
      _ ≤ (L^2*L^C*V*((K:ℝ)/x))*(X:ℝ)*(1+Real.log (X:ℝ)) :=
        giantSlotCutoff_shift_le X (giantOrdinarySlotCore e χ G x γ β) Φ hx₀ hD₀ hLip
          (fun m n _ _ _ => hA m n)
      _ ≤ (L^2*L^C*V*((K:ℝ)/x))*(T*x)*(3*L) := by gcongr
      _ = _ := by
        rw [pow_add L C 3]
        field_simp [hx₀.ne']
  have hShift := hShiftO.trans_isLittleO (giant_log_nat_power_isLittleO_x_div_log (C+3))
  refine (hTail.add hShift).congr' ?_ EventuallyEq.rfl
  filter_upwards [] with x
  change (F x-B x)+(B x-U x) = F x-U x
  ring

end
end ArtinMatthews
