module

public import ArtinMatthews.MarkedBonferroniTail
public import Mathlib.Analysis.SpecialFunctions.Sqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Numerical absorption of the actual rough-character envelope. -/

namespace ArtinMatthews

open Filter
open scoped Topology

lemma marked_rough_frequency_bound {L T t : ℝ} (hL : 0 < L)
    (ht : L^T ≤ |t|) :
    1/Real.sqrt (|t/(2*Real.pi)|) ≤ Real.sqrt (2*Real.pi)*L^(-T/2) := by
  have hp : 0 < 2*Real.pi := by positivity
  have hs : L^(T/2) ≤ Real.sqrt |t| := by
    have hh := Real.sqrt_le_sqrt ht
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL.le] at hh
    simpa only [div_eq_mul_inv, one_mul] using hh
  rw [abs_div, abs_of_pos hp, Real.sqrt_div (abs_nonneg t)]
  calc
    _ = Real.sqrt (2*Real.pi)/Real.sqrt |t| := by rw [one_div_div]
    _ ≤ Real.sqrt (2*Real.pi)/L^(T/2) :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hL _) hs
    _ = _ := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hL.le, neg_div]

lemma marked_rough_length_bound {τ δ L S : ℝ} (hδ : 0 < δ)
    (hS : Real.exp (τ*L) ≤ S) : S^(-δ) ≤ Real.exp (-(τ*δ)*L) := by
  have hh := Real.rpow_le_rpow_of_nonpos (Real.exp_pos (τ*L)) hS (by linarith : -δ ≤ 0)
  calc
    _ ≤ (Real.exp (τ*L))^(-δ) := hh
    _ = _ := by rw [← Real.exp_mul]; congr 1; ring

noncomputable def markedRoughCharacterEnvelope (A K R τ δ T L : ℝ) : ℝ :=
  3*A*K*L^R*(Real.sqrt (2*Real.pi)*L^(-T/2)+Real.exp (-(τ*δ)*L))

lemma marked_rough_character_le_envelope {A K R τ δ T L q M V S t : ℝ}
    (hA : 0 ≤ A) (hL : 0 < L) (hq : 0 ≤ q) (hM : 0 ≤ M) (hV : 0 < V)
    (hδ : 0 < δ) (hpoly : q*M/V ≤ K*L^R) (hS : Real.exp (τ*L) ≤ S)
    (ht : L^T ≤ |t|) :
    3*q*A*M/V*(1/Real.sqrt (|t/(2*Real.pi)|)+S^(-δ)) ≤
      markedRoughCharacterEnvelope A K R τ δ T L := by
  have hS0 : 0 < S := (Real.exp_pos _).trans_le hS
  have hbracket : 0 ≤ 1/Real.sqrt (|t/(2*Real.pi)|)+S^(-δ) := by positivity
  have hb := add_le_add (marked_rough_frequency_bound hL ht) (marked_rough_length_bound hδ hS)
  have hp : 0 ≤ K*L^R := (div_nonneg (mul_nonneg hq hM) hV.le).trans hpoly
  unfold markedRoughCharacterEnvelope
  calc
    _ = 3*A*(q*M/V)*(1/Real.sqrt (|t/(2*Real.pi)|)+S^(-δ)) := by ring
    _ ≤ 3*A*(K*L^R)*(1/Real.sqrt (|t/(2*Real.pi)|)+S^(-δ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (by positivity)) hbracket
    _ ≤ 3*A*(K*L^R)*(Real.sqrt (2*Real.pi)*L^(-T/2)+Real.exp (-(τ*δ)*L)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem marked_rough_character_envelope_tendsto (A K R τ δ T P : ℝ)
    (hτ : 0 < τ) (hδ : 0 < δ) (hT : R+P < T/2) :
    Tendsto (fun L : ℝ => L^P*markedRoughCharacterEnvelope A K R τ δ T L)
      atTop (𝓝 0) := by
  have h₁ := (tendsto_rpow_neg_atTop (show 0 < T/2-R-P by linarith)).const_mul
    (3*A*K*Real.sqrt (2*Real.pi))
  have h₂ := (rpow_mul_exp_neg_rpow_tendsto (P+R)
    (by norm_num : (0 : ℝ) < 1) (mul_pos hτ hδ)).const_mul (3*A*K)
  simp only [Real.rpow_one, mul_zero] at h₂
  have hh := h₁.add h₂
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hp₁ : L^(-(T/2-R-P)) = L^P*L^R*L^(-T/2) := by
    rw [← Real.rpow_add hL, ← Real.rpow_add hL]
    congr 1
    ring
  have hp₂ : L^(P+R) = L^P*L^R := Real.rpow_add hL _ _
  change 3*A*K*Real.sqrt (2*Real.pi)*L^(-(T/2-R-P)) +
    3*A*K*(L^(P+R)*Real.exp (-(τ*δ)*L)) = _
  unfold markedRoughCharacterEnvelope
  rw [hp₁, hp₂]
  ring

/-- Any frequency cutoff above the indicated polynomial threshold gives
arbitrary logarithmic saving, uniformly in all polynomially bounded data. -/
theorem marked_rough_character_uniform_power_of_cutoff (A K R τ δ T P c : ℝ)
    (hA : 0 ≤ A) (hτ : 0 < τ) (hδ : 0 < δ) (hT : R+P < T/2) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ q M V S t : ℝ,
      0 ≤ q → 0 ≤ M → 0 < V → q*M/V ≤ K*L^R →
      Real.exp (τ*L) ≤ S → L^T ≤ |t| →
      3*q*A*M/V*(1/Real.sqrt (|t/(2*Real.pi)|)+S^(-δ)) ≤ c*L^(-P) := by
  have hs := (marked_rough_character_envelope_tendsto A K R τ δ T P hτ hδ hT).eventually
    (Iio_mem_nhds hc)
  filter_upwards [hs, eventually_gt_atTop (0 : ℝ)] with L hs hL q M V S t hq hM hV hpoly hS ht
  have hpow : 0 < L^P := Real.rpow_pos_of_pos hL P
  have he := marked_rough_character_le_envelope hA hL hq hM hV hδ hpoly hS ht
  have hid : L^P*L^(-P) = 1 := by rw [← Real.rpow_add hL]; simp
  apply (mul_le_mul_iff_of_pos_left hpow).mp
  calc
    _ ≤ L^P*markedRoughCharacterEnvelope A K R τ δ T L := mul_le_mul_of_nonneg_left he hpow.le
    _ ≤ c := hs.le
    _ = _ := by rw [mul_left_comm, hid, mul_one]

theorem marked_rough_character_uniform_power (A K R τ δ P c : ℝ)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hP : 0 ≤ P) (hτ : 0 < τ) (hδ : 0 < δ) (hc : 0 < c) :
    ∃ T : ℝ, 0 < T ∧ ∀ᶠ L : ℝ in atTop, ∀ q M V S t : ℝ,
      0 ≤ q → 0 ≤ M → 0 < V → q*M/V ≤ K*L^R →
      Real.exp (τ*L) ≤ S → L^T ≤ |t| →
      3*q*A*M/V*(1/Real.sqrt (|t/(2*Real.pi)|)+S^(-δ)) ≤ c*L^(-P) := by
  refine ⟨2*(R+P+1), by linarith, ?_⟩
  exact marked_rough_character_uniform_power_of_cutoff A K R τ δ (2*(R+P+1)) P c
    hA hτ hδ (by linarith) hc

end ArtinMatthews
