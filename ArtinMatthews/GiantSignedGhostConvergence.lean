module

public import ArtinMatthews.GiantSignedGhostAbsoluteRow


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence of every original ghost birth series on an
exponentially bounded test. No birth cutoff is used. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedGhostBirthContribution {P : Finset ℕ} (ν : P → ℝ) (C : ℂ)
    (m : GiantSignedGroupMemory P) (deleted : Finset (Fin m.1))
    (f : GiantSignedGroupMemory P → ℂ) (b : ℕ) : ℂ :=
  (C ^ b / (Nat.factorial b : ℂ)) *
    ∑ born : Fin b → P, (∏ i, (ν (born i) : ℂ)) * f (giantSignedGhostTarget m deleted born)

private theorem ghostBirthMajorant_hasSum {P : Finset ℕ} (ν : P → ℝ) (C : ℂ)
    (m : GiantSignedGroupMemory P) (deleted : Finset (Fin m.1)) (B v : ℝ) :
    HasSum (fun b : ℕ => (‖C‖ ^ b / (Nat.factorial b : ℝ)) *
      ∑ born : Fin b → P, (∏ i, ν (born i)) * (B * v ^ (giantSignedGhostTarget m deleted born).1))
      ((B * v ^ (m.1 - deleted.card)) * Real.exp (‖C‖ * (∑ p : P, ν p) * v)) := by
  convert (giantSignedGhost_birthSeries_hasSum ν ‖C‖ v).mul_left
    (B * v ^ (m.1 - deleted.card)) using 1
  funext b
  simp only [giantSignedGhostTarget_degree, pow_add, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro born _
  ring

theorem giantSignedGhostBirthContribution_norm_le {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (C : ℂ)
    (m : GiantSignedGroupMemory P) (deleted : Finset (Fin m.1))
    (f : GiantSignedGroupMemory P → ℂ) (B v : ℝ)
    (hf : ∀ x, ‖f x‖ ≤ B * v ^ x.1) (b : ℕ) :
    ‖giantSignedGhostBirthContribution ν C m deleted f b‖ ≤
      (‖C‖ ^ b / (Nat.factorial b : ℝ)) *
        ∑ born : Fin b → P, (∏ i, ν (born i)) * (B * v ^ (giantSignedGhostTarget m deleted born).1) := by
  classical
  unfold giantSignedGhostBirthContribution
  rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ born : Fin b → P, ‖(∏ i, (ν (born i) : ℂ)) * f (giantSignedGhostTarget m deleted born)‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro born _
      rw [norm_mul, norm_prod]
      have hn : (∏ i, ‖(ν (born i) : ℂ)‖) = ∏ i, ν (born i) := by
        apply Finset.prod_congr rfl
        intro i _
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hν _)]
      rw [hn]
      exact mul_le_mul_of_nonneg_left (hf _) (Finset.prod_nonneg fun i _ => hν _)

theorem giantSignedGhostBirthContribution_summable_norm {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (C : ℂ)
    (m : GiantSignedGroupMemory P) (deleted : Finset (Fin m.1))
    (f : GiantSignedGroupMemory P → ℂ) (B v : ℝ)
    (hf : ∀ x, ‖f x‖ ≤ B * v ^ x.1) :
    Summable (fun b => ‖giantSignedGhostBirthContribution ν C m deleted f b‖) := by
  exact (ghostBirthMajorant_hasSum ν C m deleted B v).summable.of_nonneg_of_le
    (fun _ => norm_nonneg _) (giantSignedGhostBirthContribution_norm_le ν hν C m deleted f B v hf)

theorem giantSignedGhostBirthContribution_summable {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (C : ℂ)
    (m : GiantSignedGroupMemory P) (deleted : Finset (Fin m.1))
    (f : GiantSignedGroupMemory P → ℂ) (B v : ℝ)
    (hf : ∀ x, ‖f x‖ ≤ B * v ^ x.1) :
    Summable (giantSignedGhostBirthContribution ν C m deleted f) :=
  (giantSignedGhostBirthContribution_summable_norm ν hν C m deleted f B v hf).of_norm

theorem giantSignedGhostBirthContribution_tsum_norm_le {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (C : ℂ)
    (m : GiantSignedGroupMemory P) (deleted : Finset (Fin m.1))
    (f : GiantSignedGroupMemory P → ℂ) (B v : ℝ)
    (hf : ∀ x, ‖f x‖ ≤ B * v ^ x.1) :
    ‖∑' b, giantSignedGhostBirthContribution ν C m deleted f b‖ ≤
      (B * v ^ (m.1 - deleted.card)) * Real.exp (‖C‖ * (∑ p : P, ν p) * v) :=
  tsum_of_norm_bounded (ghostBirthMajorant_hasSum ν C m deleted B v)
    (giantSignedGhostBirthContribution_norm_le ν hν C m deleted f B v hf)

end
end ArtinMatthews
