module

public import ArtinMatthews.MarkedRoughLogAbel
public import ArtinMatthews.MarkedMajorArcLowMangoldt
public import ArtinMatthews.MarkedMajorArcPrimePowerLog
public import ArtinMatthews.MarkedMajorArcPrimePowerAbsorption


set_option backward.privateInPublic true
@[expose] public section

/-! The actual all-character prime interval count with its dy/log y main term. -/
namespace ArtinMatthews
open Finset MeasureTheory Filter ArithmeticFunction
open scoped BigOperators Topology
noncomputable section

def markedRoughPrimeIntervalSum {q : ℕ} (χ : DirichletCharacter ℂ q) (u v : ℝ) : ℂ :=
  ∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, χ (p : ZMod q)

theorem marked_prime_interval_count_of_mangoldt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {u v D : ℝ} (hu : 0 < u)
    (hlog : 1 ≤ Real.log u) (huv : u ≤ v) (hvu : v ≤ 2 * u) (hD : 0 ≤ D)
    (hprefix : ∀ w ∈ Set.Icc u v,
      ‖(∑ n ∈ Ioc 0 ⌊w⌋₊, χ (n : ZMod q) * (vonMangoldt n : ℂ)) -
        (if χ = 1 then (w : ℂ) else 0)‖ ≤ D) :
    ‖markedRoughPrimeIntervalSum χ u v -
      (if χ = 1 then ((∫ t in u..v, (Real.log t)⁻¹ : ℝ) : ℂ) else 0)‖ ≤
      3 * D + 2 * Real.sqrt v * Real.log v := by
  classical
  let a : ℕ → ℂ := fun n => χ (n : ZMod q) * (vonMangoldt n : ℂ)
  let m : ℂ := if χ = 1 then 1 else 0
  let W : ℂ := ∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, ((Real.log n)⁻¹ : ℝ) * a n
  have hpref (w : ℝ) (hw : w ∈ Set.Icc u v) :
      ‖(∑ n ∈ Icc 0 ⌊w⌋₊, a n) - m * (w : ℂ)‖ ≤ D := by
    rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons]
    simpa [a, m] using hprefix w hw
  have hb : ‖W - (if χ = 1 then ((∫ t in u..v, (Real.log t)⁻¹ : ℝ) : ℂ) else 0)‖ ≤
      3 * D := by
    simpa [W, m] using
      marked_log_weight_centered_interval_bound a m hu hlog huv hvu hD hpref
  have hpower : ‖W - markedRoughPrimeIntervalSum χ u v‖ ≤
      2 * Real.sqrt v * Real.log v := by
    have h := marked_major_log_prime_power_error χ 0 1 (by norm_num) hu hlog huv
    simpa [W, a, markedMajorLogMangoldtSum, markedMajorNormalizedPrimeSum,
      markedRoughPrimeIntervalSum, mul_comm, mul_left_comm, mul_assoc] using h
  calc
    _ ≤ ‖W - (if χ = 1 then ((∫ t in u..v, (Real.log t)⁻¹ : ℝ) : ℂ) else 0)‖ +
        ‖markedRoughPrimeIntervalSum χ u v - W‖ := by
      have he : markedRoughPrimeIntervalSum χ u v -
          (if χ = 1 then ((∫ t in u..v, (Real.log t)⁻¹ : ℝ) : ℂ) else 0) =
          (W - (if χ = 1 then ((∫ t in u..v, (Real.log t)⁻¹ : ℝ) : ℂ) else 0)) +
            (markedRoughPrimeIntervalSum χ u v - W) := by ring
      rw [he]
      exact norm_add_le _ _
    _ ≤ _ := add_le_add hb (by simpa only [norm_sub_rev] using hpower)

theorem marked_rough_prime_slot_siegel_walfisz (a η τ P : ℝ)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hP : 0 ≤ P) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (H u v : ℝ),
        (q : ℝ) ≤ L ^ a → Real.exp (τ * L) ≤ H → H ≤ u → u ≤ v → v ≤ 2 * H →
        v ≤ Real.exp (η * L) →
        ‖markedRoughPrimeIntervalSum χ u v -
          (if χ = 1 then ((∫ t in u..v, (Real.log t)⁻¹ : ℝ) : ℂ) else 0)‖ ≤
          C * H * L ^ (-P) := by
  obtain ⟨K, hK, hSW⟩ := marked_major_mangoldt_prefix_low a η τ P ha hη hτ hP
  refine ⟨6 * K + 2, by positivity, ?_⟩
  filter_upwards [hSW, marked_major_prime_power_uniform_power P η τ 1 hP hτ hη
    (by norm_num), eventually_ge_atTop (max 1 (1 / τ))] with L hSW hpower hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hτL : 1 ≤ τ * L := by
    have hh := (le_max_right (1 : ℝ) (1 / τ)).trans hL
    have := (div_le_iff₀ hτ).mp hh
    nlinarith
  intro q _ χ H u v hq hH hHu huv hvH hv
  have hH0 : 0 < H := (Real.exp_pos _).trans_le hH
  have hu0 : 0 < u := hH0.trans_le hHu
  have hlog : 1 ≤ Real.log u := hτL.trans
    ((Real.le_log_iff_exp_le hu0).mpr (hH.trans hHu))
  have hD : 0 ≤ 2 * K * H * L ^ (-P) := by positivity
  have hpref (w : ℝ) (hw : w ∈ Set.Icc u v) :
      ‖(∑ n ∈ Ioc 0 ⌊w⌋₊, χ (n : ZMod q) * (vonMangoldt n : ℂ)) -
        (if χ = 1 then (w : ℂ) else 0)‖ ≤ 2 * K * H * L ^ (-P) := by
    exact (hSW q χ w hq (hH.trans (hHu.trans hw.1)) (hw.2.trans hv)).trans (by
      have hwH : w ≤ 2 * H := hw.2.trans hvH
      nlinarith [mul_le_mul_of_nonneg_left hwH (mul_nonneg hK.le
        (Real.rpow_nonneg hL0.le (-P)))])
  have hcount := marked_prime_interval_count_of_mangoldt χ hu0 hlog huv
    (hvH.trans (by linarith)) hD hpref
  have hpp := hpower u v (hH.trans hHu) huv (hvH.trans (by linarith)) hv
  have hpp' : 2 * Real.sqrt v * Real.log v ≤ 2 * H * L ^ (-P) := by
    have hh : 2 * Real.sqrt v * Real.log v ≤ u * L ^ (-P) := by
      simpa only [one_mul, mul_one, mul_comm] using (div_le_iff₀ hu0).mp hpp
    exact hh.trans (mul_le_mul_of_nonneg_right (huv.trans hvH)
      (Real.rpow_nonneg hL0.le (-P)))
  exact hcount.trans (by nlinarith)

end
end ArtinMatthews
