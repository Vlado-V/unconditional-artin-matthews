module

public import ArtinMatthews.PrimeExtractionSeparatedCoefficients
public import ArtinMatthews.HeckeCubicPrimeIntervals


set_option backward.privateInPublic true
@[expose] public section

/-! The literal section-eight first coefficient is an actual prime sum
on a truncated interval, with the exact retained Mellin frequency. -/

noncomputable section
namespace ArtinMatthews
open OAI.SevenEighths Filter
open scoped BigOperators Classical

theorem primeExtractionFirstPhaseCoefficient_interval_test
    (η : HeckeFamily.Character) {r q : ℕ} (χ : DirichletCharacter ℂ r)
    (ϑ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (v t : ℝ) (m n : ℕ) :
    markedTwistedSum (Finset.Icc m n) (primeExtractionFirstPhaseCoefficient η χ z v) ϑ t =
      ∑ p ∈ (Finset.Icc (max m (⌊z⌋₊+1)) n).filter Nat.Prime,
        idealThetaCoeff η p*χ p*ϑ p*(p : ℂ)^(((t+2*Real.pi*v : ℝ) : ℂ)*Complex.I) := by
  rw [primeExtractionFirstPhaseCoefficient_twistedSum]
  have hset : (Finset.Icc m n).filter (fun p : ℕ => p.Prime ∧ z<(p : ℝ)) =
      (Finset.Icc (max m (⌊z⌋₊+1)) n).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, max_le_iff]
    constructor
    · rintro ⟨⟨hm, hn⟩, hp, hzP⟩
      exact ⟨⟨⟨hm, Nat.succ_le_iff.mpr ((Nat.floor_lt hz).mpr hzP)⟩, hn⟩, hp⟩
    · rintro ⟨⟨⟨hm, hzP⟩, hn⟩, hp⟩
      exact ⟨⟨hm, hn⟩, hp, (Nat.floor_lt hz).mp (Nat.succ_le_iff.mp hzP)⟩
  rw [← hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime ∧ z<(p : ℝ)
  · rw [roughPrimeFirstCoefficient, ite_eq_left hp, ite_eq_left hp]
    have he : markedLogTwist p (t+2*Real.pi*v) =
        (p : ℂ)^(((t+2*Real.pi*v : ℝ) : ℂ)*Complex.I) := by
      rw [markedLogTwist_eq_cpow hp.1.pos]
      congr 1
      ring
    rw [he]
  · simp only [roughPrimeFirstCoefficient, ite_eq_right hp, zero_mul]

theorem primeExtraction_retained_frequency_bound (B R : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ x : ℝ in atTop, ∀ t v : ℝ, |t| ≤ x^B → |v| ≤ (Real.log x)^R →
      |t+2*Real.pi*v| ≤ x^(B+2) := by
  have hlog := (isLittleO_log_rpow_rpow_atTop R (show (0 : ℝ) < 1 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hlog, eventually_ge_atTop (1+2*Real.pi),
    eventually_gt_atTop (1 : ℝ)] with x hlog hxlarge hx
  intro t v ht hv
  have hx0 : 0 < x := by linarith
  have hlog' : (Real.log x)^R ≤ x := by
    simpa only [Real.rpow_one, one_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Real.log_pos hx).le _), abs_of_pos hx0] using hlog
  have hxB : x ≤ x^(B+1) := by
    calc
      x = x^(1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hBt : |t| ≤ x^(B+1) := ht.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
  have hBv : |v| ≤ x^(B+1) := hv.trans (hlog'.trans hxB)
  calc
    _ ≤ |t|+2*Real.pi*|v| := by simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (show (0:ℝ)<2 by norm_num)] using norm_add_le t (2*Real.pi*v)
    _ ≤ (1+2*Real.pi)*x^(B+1) := by nlinarith [Real.pi_pos]
    _ ≤ x*x^(B+1) := mul_le_mul_of_nonneg_right hxlarge (Real.rpow_nonneg hx0.le _)
    _ = x^(1 : ℝ)*x^(B+1) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring

end ArtinMatthews
