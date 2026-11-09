module

public import ArtinMatthews.GiantMarkedSelectedSquareError
public import ArtinMatthews.GiantActualRoughSieve
public import ArtinMatthews.MarkedMajorTypeIIBands
public import ArtinMatthews.MarkedTypeIICollisionDecay
public import ArtinMatthews.MarkedProgressionGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! The square-divisibility replacement on the actual PD03 bands and
positive-power rectangle scales. The onset is uniform in the rectangle,
bounded invariant test, and logarithmically bounded coefficients. -/

noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

theorem giant_marked_quotient_damping_log_saving {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j, (1 / 10 : ℝ) < e j ∧ e j < (1 / 5 : ℝ))
    (δ C D A : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) (Real.exp L)
      ∀ (Hm Hn : ℝ) (M N : Finset ℕ) (α β F : ℕ → ℂ),
        Real.exp (δ * L) ≤ Hm → Real.exp (δ * L) ≤ Hn →
        (∀ m ∈ M, Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm) →
        (∀ n ∈ N, Hn ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Hn) →
        (∀ m ∈ M, ‖α m‖ ≤ L ^ C) → (∀ n ∈ N, ‖β n‖ ≤ L ^ D) →
        (∀ u, ‖F u‖ ≤ 1) → (∀ j p, p ∈ P j → ∀ h, F (p * h) = F h) →
        ‖(∑ m ∈ M, ∑ n ∈ N, α m * β n * F (m * n - 1) *
          (literalMarkedArrayWeight e (Real.exp L) (m * n - 1) : ℂ)) -
          giantMarkedQuotientDampedSum P M N α β F‖ ≤ Hm * Hn * L ^ (-A) := by
  classical
  let S := ((Real.log 2 / 2)⁻¹ : ℝ) ^ Fintype.card J
  have hsmall := Real.tendsto_exp_atTop.eventually
    (marked_sublinear_log_exp_le_rpow_eventually (1 / 5) 4 δ (by norm_num) hδ)
  have ht := (marked_bands_reciprocal_square_log_saving Finset.univ e
    (fun j _ => (he j).1.le) (C + D + A)).const_mul (9 * S)
  simp only [mul_zero] at ht
  have hdecay := Real.tendsto_exp_atTop.eventually (ht.eventually (gt_mem_nhds zero_lt_one))
  filter_upwards [markedMajorTypeII_band_data e hinj he 0, hsmall, hdecay,
    eventually_gt_atTop (0 : ℝ)] with L hb hsmall hdecay hL
  let P := fun j => markedLogPowerBand (e j) (Real.exp L)
  let U := Finset.univ.biUnion P
  let R := ∑ p ∈ U, 1 / (p : ℝ) ^ 2
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => by positivity)
  have hscalar : (9 * S) * (L ^ (C + D + A) * R) ≤ 1 := by
    have h : (9 * S) * (Real.log (Real.exp L) ^ (C + D + A) * R) < 1 := hdecay
    rw [Real.log_exp] at h
    exact h.le
  have hscale : Real.exp (4 * L ^ (1 / 5 : ℝ)) ≤ Real.exp (δ * L) := by
    change Real.exp (4 * (Real.log (Real.exp L)) ^ (1 / 5 : ℝ)) ≤ (Real.exp L) ^ δ at hsmall
    simpa only [Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos L), mul_comm L δ] using hsmall
  have hV (j : J) : 0 < bandReciprocalMass (P j) :=
    (show 0 < Real.log 2 / 2 by positivity).trans_le (hb.2.2.1 j)
  have hm₀ : 0 ≤ markedMajorLabelMass P := (markedMajorLabelMass_pos P hV).le
  have hmass : markedMajorLabelMass P ≤ S := by
    calc
      _ ≤ ∏ _j : J, ((Real.log 2 / 2)⁻¹ : ℝ) :=
        Finset.prod_le_prod₀ (fun j _ => inv_nonneg.mpr (hV j).le)
          (fun j _ => (inv_le_inv₀ (hV j) (by positivity)).mpr (hb.2.2.1 j))
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, S]
  dsimp only
  intro Hm Hn M N α β F hHm hHn hM hN hα hβ hFnorm hF
  have h1 : 1 ≤ Real.exp (δ * L) := Real.one_le_exp_iff.mpr (mul_nonneg hδ.le hL.le)
  have hm1 : 1 ≤ Hm := h1.trans hHm
  have hn1 : 1 ≤ Hn := h1.trans hHn
  have hp (p : ℕ) (hp : p ∈ U) : 0 < p ∧ (p : ℝ) ^ 2 ≤ Hn := by
    obtain ⟨j, _, hp⟩ := Finset.mem_biUnion.mp hp
    have hj := hb.2.1 j p hp
    refine ⟨hj.1.pos, ?_⟩
    have hup := (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hj.1.pos)).mp hj.2.2
    calc
      _ ≤ Real.exp (2 * L ^ (1 / 5 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hup 2
      _ = Real.exp (4 * L ^ (1 / 5 : ℝ)) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := hscale.trans hHn
  have hcount := giantMarkedSquareCount_le U M N hm1 hn1
    (fun m hm => ⟨Nat.cast_pos.mp (zero_lt_one.trans_le (hm1.trans (hM m hm).1)), (hM m hm).2⟩)
    (fun n hn => ⟨Nat.cast_pos.mp (zero_lt_one.trans_le (hn1.trans (hN n hn).1)), (hN n hn).2⟩)
    hp
  have hC : 0 ≤ L ^ C := Real.rpow_nonneg hL.le _
  have hD : 0 ≤ L ^ D := Real.rpow_nonneg hL.le _
  have herr := giantMarkedQuotientDampedSum_error P
    (fun j p hp => (hb.2.1 j p hp).1) hb.1 hV M N α β F hC hD hα hβ hFnorm hF
  have hbudget : L ^ C * L ^ D * S * (9 * R) ≤ L ^ (-A) := by
    rw [Real.rpow_neg hL.le, ← one_div (L ^ A)]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hL A)).mpr
    calc
      _ = (9 * S) * (L ^ (C + D + A) * R) := by
        rw [Real.rpow_add hL, Real.rpow_add hL]
        ring
      _ ≤ _ := hscalar
  apply herr.trans
  calc
    _ ≤ (L ^ C * L ^ D * S) * (9 * Hm * Hn * R) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hmass (mul_nonneg hC hD))
        hcount (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hC hD) (hm₀.trans hmass))
    _ = Hm * Hn * (L ^ C * L ^ D * S * (9 * R)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbudget
      (mul_nonneg (zero_le_one.trans hm1) (zero_le_one.trans hn1))

end ArtinMatthews
