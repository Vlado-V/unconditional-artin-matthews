module

public import ArtinMatthews.IdealSourceParameterDefinitions
public import ArtinMatthews.IdealResidualNumerics


set_option backward.privateInPublic true
@[expose] public section

/-! Choose the probe number first, then the comparison precision.
All growing group and probe counts are quantified after that choice. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem idealSource_probe_sqrt_le {L D θ : ℝ} {s : ℕ}
    (hL : 0 < L) (hθ : 0 ≤ θ) (hbound : θ^s ≤ L^(-2*D)) :
    Real.sqrt (θ^s) ≤ L^(-D) := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.rpow_nonneg hL.le _)).mp
  rw [Real.sq_sqrt (pow_nonneg hθ s)]
  have he : (L^(-D))^2=L^(-2*D) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hL.le]
    congr 1
    ring
  rw [he]
  exact hbound

theorem idealSource_probe_count {L C₀ : ℝ} {m b P : ℕ}
    (hb : (b : ℝ) ≤ C₀*Real.log L) (hP : P ≤ m*b) :
    (P : ℝ) ≤ ((m : ℝ)*C₀)*Real.log L := by
  calc
    _ ≤ (m : ℝ)*(b : ℝ) := by exact_mod_cast hP
    _ ≤ (m : ℝ)*(C₀*Real.log L) :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ = _ := by ring

theorem idealSource_scalar_choice (c₀ C₀ E : ℝ) (ell : ℕ)
    (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hE : 0 ≤ E) :
    ∃ m : ℕ, 1 ≤ m ∧ 0 < (2/(m+1 : ℕ) : ℝ) ∧ (2/(m+1 : ℕ) : ℝ) < 1 ∧
      (∀ J : ℕ, idealSourceDimensionThreshold m ell ≤ J →
        m ≤ J ∧ (m+ell)*(m+ell-1) ≤ J+ell) ∧
      ∀ (L : ℝ) (b s₁ s₂ P : ℕ), 2 ≤ L → (b : ℝ) ≤ C₀*Real.log L → P ≤ m*b →
        c₀*Real.log L/3 ≤ s₁ → c₀*Real.log L/3 ≤ s₂ →
        Real.sqrt ((2/(m+1 : ℕ) : ℝ)^s₁)+Real.sqrt ((2/(m+1 : ℕ) : ℝ)^s₂)+
          (2 : ℝ)^P*L^(-idealSourceErrorExponent E C₀ m) ≤ L^(-E) := by
  obtain ⟨m, hm, hθ, hθ1, hblock⟩ :=
    idealProbe_logarithmic_block_choice c₀ (E+3) hc₀ (by positivity)
  refine ⟨m, hm, hθ, hθ1, idealSourceDimensionThreshold_spec m ell, ?_⟩
  intro L b s₁ s₂ P hL hb hP hs₁ hs₂
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have h₁ := idealSource_probe_sqrt_le hLpos hθ.le (hblock L s₁ hL1 hs₁)
  have h₂ := idealSource_probe_sqrt_le hLpos hθ.le (hblock L s₂ hL1 hs₂)
  have herr := idealResidualNorm_absorb L ((m : ℝ)*C₀) E (idealSourceErrorExponent E C₀ m) P
    hL (idealSource_probe_count hb hP) (idealSourceErrorExponent_margin hC₀ m)
  linarith

end
end ArtinMatthews
