module

public import ArtinMatthews.MarkedMajorArcCenteredCoefficient
public import ArtinMatthews.MarkedMajorArcLogPhaseWeight
public import ArtinMatthews.MarkedMajorArcPrimePowerLog


set_option backward.privateInPublic true
@[expose] public section

/-! Exact passage from centered sharp Mangoldt-minus-rough prefixes to the
literal modulated long coefficient. No main term remains after centering. -/
namespace ArtinMatthews
open Finset ArithmeticFunction

noncomputable def markedCenteredMangoldt {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W : ℝ) (n : ℕ) : ℂ := by
  classical
  exact χ (n:ZMod q)*((vonMangoldt n:ℂ)-
    (markedSieveEulerProduct W:ℂ)⁻¹*
      (if ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p∣n then (1:ℂ) else 0))

 theorem marked_centered_mangoldt_log_sum_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W t H u v : ℝ) :
    (H:ℂ)⁻¹*∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,
      ((Real.log n)⁻¹:ℝ)*(n:ℂ)^((t:ℂ)*Complex.I)*markedCenteredMangoldt χ W n =
      markedMajorLogMangoldtSum χ t H u v-markedRoughCharacterSum χ W t H u v := by
  classical
  rw [markedMajorLogMangoldtSum,markedRoughCharacterSum]
  simp only [Complex.ofReal_mul,mul_inv_rev]
  rw [mul_assoc (markedSieveEulerProduct W:ℂ)⁻¹ (H:ℂ)⁻¹, mul_left_comm (markedSieveEulerProduct W:ℂ)⁻¹]
  rw [← mul_sub]
  congr 1
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  dsimp [markedCenteredMangoldt]
  ring

 theorem marked_centered_prefix_partial_summation {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (W modulation t H : ℝ) {u v D : ℝ}
    (hH : 0 < H) (hHu : H ≤ u) (huv : u ≤ v) (hvH : v ≤ 2*H)
    (hlog : 1 ≤ Real.log u) (hD : 0 ≤ D)
    (hprefix : ∀ w ∈ Set.Icc u v, ‖∑ n ∈ Ioc ⌊u⌋₊ ⌊w⌋₊, markedCenteredMangoldt χ W n‖ ≤ D) :
    ‖markedMajorCenteredSum χ W modulation t H u v‖ ≤
      (D/H)*(|t+modulation|+3)+2*Real.sqrt v*Real.log v/H := by
  have hu : 0 < u := hH.trans_le hHu
  have hweight := marked_log_phase_interval_bound (markedCenteredMangoldt χ W)
    (t+modulation) hu hlog huv (hvH.trans (by linarith)) hD hprefix
  have hcentered : ‖markedMajorLogMangoldtSum χ (t+modulation) H u v-
      markedRoughCharacterSum χ W (t+modulation) H u v‖ ≤ (D/H)*(|t+modulation|+3) := by
    rw [← marked_centered_mangoldt_log_sum_eq,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hH]
    calc
      _ ≤ H⁻¹*(D*(|t+modulation|+3)) := mul_le_mul_of_nonneg_left hweight (inv_nonneg.mpr hH.le)
      _ = _ := by ring
  have hpower := marked_major_log_prime_power_error χ (t+modulation) H hH hu hlog huv
  rw [marked_centered_sum_eq χ W modulation t H u v hu.le]
  have he : markedMajorNormalizedPrimeSum χ (t+modulation) H u v-
      markedRoughCharacterSum χ W (t+modulation) H u v =
      (markedMajorLogMangoldtSum χ (t+modulation) H u v-markedRoughCharacterSum χ W (t+modulation) H u v)-
      (markedMajorLogMangoldtSum χ (t+modulation) H u v-markedMajorNormalizedPrimeSum χ (t+modulation) H u v) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hcentered hpower)

end ArtinMatthews
