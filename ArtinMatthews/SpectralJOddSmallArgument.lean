module

public import ArtinMatthews.SpectralJHolomorphicCoefficient


set_option backward.privateInPublic true
@[expose] public section

/-! A summable odd-order majorant retains the extra small-argument factor.
It will give absolute weight-and-modulus convergence at the infinity cusp. -/
noncomputable section
open Set

namespace ArtinMatthews

theorem spectralJOddSynthesisTerm_small_argument (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ (j : ℕ) (c : ℝ), 1 ≤ c →
      ‖spectralJOddSynthesisTerm f j (Q/c)‖ ≤
        (C*(A^(2*j+1)/((2*j+1).factorial : ℝ)))/c := by
  obtain ⟨C₀,A₀,hC₀,hA₀,hcoeff⟩ := spectralJDiscreteCoefficient_factorial_bound f hf hc hp
  refine ⟨2*C₀*Real.exp (Q^2/4),A₀*Q/2,by positivity,by positivity,?_⟩
  intro j c hc
  let u : ℝ := 1/c
  have hcp : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; exact (div_le_one hcp).mpr hc
  have hQu : 0 ≤ Q*u := mul_nonneg hQ hu
  have hQuQ : Q*u ≤ Q := mul_le_of_le_one_right hQ hu1
  have hsq : (Q*u)^2 ≤ Q^2 := (sq_le_sq₀ hQu hQ).mpr hQuQ
  have hpow : u^(2*j+1) ≤ u := by
    simpa using pow_le_pow_of_le_one hu hu1 (show 1 ≤ 2*j+1 by omega)
  have hx : Q/c = Q*u := by dsimp [u]; ring
  rw [hx]
  calc
    _ ≤ 2*C₀*Real.exp ((Q*u)^2/4)*
        ((A₀*(|Q*u|/2))^(2*j+1)/((2*j+1).factorial : ℝ)) :=
      spectralJOddSynthesisTerm_norm_le f hC₀ hA₀ hcoeff j (Q*u)
    _ = (2*C₀)*Real.exp ((Q*u)^2/4)*
        ((A₀*Q/2)^(2*j+1)/((2*j+1).factorial : ℝ))*u^(2*j+1) := by
      rw [abs_of_nonneg hQu,show A₀*(Q*u/2) = (A₀*Q/2)*u by ring,mul_pow]
      ring
    _ ≤ (2*C₀)*Real.exp (Q^2/4)*
        ((A₀*Q/2)^(2*j+1)/((2*j+1).factorial : ℝ))*u := by gcongr
    _ = _ := by dsimp [u]; ring

theorem spectralJOddMajorant_summable (C A : ℝ) :
    Summable (fun j : ℕ => C*(A^(2*j+1)/((2*j+1).factorial : ℝ))) := by
  exact ((NormedSpace.expSeries_div_hasSum_exp A).summable.comp_injective
    (show Function.Injective (fun j : ℕ => 2*j+1) from fun a b h => by dsimp only at h; omega)).mul_left C

end ArtinMatthews
