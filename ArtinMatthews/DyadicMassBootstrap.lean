module

public import ArtinMatthews.DyadicShellBootstrap


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
noncomputable section

/-- A positive power saving in the shell recurrence forces arbitrarily strong dyadic decay. -/
theorem dyadic_mass_arbitrary_decay
    (a : ℕ → ℝ) (δ D B C : ℝ) (ha : ∀ n, 0 ≤ a n)
    (hδ : 0 < δ) (hD : 0 ≤ D) (hC : 0 < C)
    (hbound : ∀ n, a n ≤ C * (2 : ℝ) ^ (B * (n : ℝ)))
    (hrec : ∀ n, a (n + 1) ≤ D * (2 : ℝ) ^ (-δ * ((n + 1 : ℕ) : ℝ)) *
      (a n + a (n + 1) + a (n + 2))) (b : ℝ) :
    ∃ C' > 0, ∀ n, a n ≤ C' * (2 : ℝ) ^ (b * (n : ℝ)) := by
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hr : 0 < (2 : ℝ) ^ (-δ) := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-δ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hb : ∀ n, a n ≤ C * ((2 : ℝ) ^ B) ^ n := by
    simpa only [Real.rpow_mul_natCast htwo] using hbound
  have hre : ∀ n, a (n + 1) ≤ D * ((2 : ℝ) ^ (-δ)) ^ (n + 1) *
      (a n + a (n + 1) + a (n + 2)) := by
    simpa only [Real.rpow_mul_natCast htwo] using hrec
  obtain ⟨C',hC',hc⟩ := shell_recurrence_arbitrary_rate a ((2 : ℝ)^(-δ)) D
    ((2 : ℝ)^B) C ha hr hr1 hD (Real.rpow_pos_of_pos (by norm_num) _) hC hb hre
    ((2 : ℝ)^b) (Real.rpow_pos_of_pos (by norm_num) _)
  exact ⟨C',hC',by simpa only [Real.rpow_mul_natCast htwo] using hc⟩

/-- In particular the dyadic masses have a finite total. -/
theorem dyadic_mass_summable
    (a : ℕ → ℝ) (δ D B C : ℝ) (ha : ∀ n, 0 ≤ a n)
    (hδ : 0 < δ) (hD : 0 ≤ D) (hC : 0 < C)
    (hbound : ∀ n, a n ≤ C * (2 : ℝ) ^ (B * (n : ℝ)))
    (hrec : ∀ n, a (n + 1) ≤ D * (2 : ℝ) ^ (-δ * ((n + 1 : ℕ) : ℝ)) *
      (a n + a (n + 1) + a (n + 2))) : Summable a := by
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hr : 0 < (2 : ℝ) ^ (-δ) := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-δ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hb : ∀ n, a n ≤ C * ((2 : ℝ) ^ B) ^ n := by
    simpa only [Real.rpow_mul_natCast htwo] using hbound
  have hre : ∀ n, a (n + 1) ≤ D * ((2 : ℝ) ^ (-δ)) ^ (n + 1) *
      (a n + a (n + 1) + a (n + 2)) := by
    simpa only [Real.rpow_mul_natCast htwo] using hrec
  exact shell_recurrence_summable a ((2 : ℝ)^(-δ)) D ((2 : ℝ)^B) C ha
    hr hr1 hD (Real.rpow_pos_of_pos (by norm_num) _) hC hb hre

end
end ArtinMatthews
