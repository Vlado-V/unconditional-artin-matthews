module

public import ArtinMatthews.MarkedMinorArcBudget
public import ArtinMatthews.MarkedMinorArcRate
public import ArtinMatthews.MarkedMinorArcDiophantine


set_option backward.privateInPublic true
@[expose] public section

/-!
# Actual clean determinant-frequency decay

This is the finite determinant exponential estimate in PD (mem:minor-decay),
with its rational approximation derived from the actual shifted minor arcs.
The exponent G+2 is chosen from G alone. Fixed geometric constants affect
only the threshold, and the marking-band exponents do not occur.
-/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology

/-- Every actual shifted minor-arc determinant transform has the prescribed
L² decay, uniformly over origins, coefficients and all source lattice boxes. -/
theorem marked_minor_clean_determinant_energy {G C H : ℝ}
    (hG : 0 < G) (hC : 1 ≤ C) (hH : 1 ≤ H) :
    ∀ᶠ Λ : ℝ in atTop, ∀ (Y : ℝ) (L T : ℤ) (M N : ℕ) (θ t : ℝ) (c : ℤ × ℤ → ℂ),
      Real.exp (Λ^(1/10 : ℝ)) ≤ Y → Y ≤ Real.exp (H*Λ^(1/5 : ℝ)) →
      1 ≤ M → 1 ≤ N → (M : ℝ)*(N : ℝ) ≤ C*Y →
      (M : ℝ) ≤ C*Y^(9/10 : ℝ) → (N : ℝ) ≤ C*Y^(9/10 : ℝ) →
      ¬MarkedInMajorArcs θ (Λ^(G+2)) Y → |t| ≤ Λ^(G+2)/2 →
      (∑ h₁ ∈ Finset.Ico L (L+(M : ℤ)), ∑ h₂ ∈ Finset.Ico T (T+(N : ℤ)),
        ‖((Y : ℂ)⁻¹) * markedMinorDeterminantTransform L T M N (θ+t/Y) c h₁ h₂‖^2) ≤
        Λ^(-2*G) *
          (∑ l₁ ∈ Finset.Ico L (L+(M : ℤ)), ∑ l₂ ∈ Finset.Ico T (T+(N : ℤ)), ‖c (l₁,l₂)‖^2) := by
  have hA : 0 < G+2 := by linarith
  filter_upwards [marked_minor_clean_rate_eventually G hC hH,
    marked_minor_logarithmic_cutoff hA,eventually_ge_atTop (1:ℝ)]
      with Λ hrate hcut hΛ Y L T M N θ t c hYlo hYhi hMpos hNpos hMN hM hN hminor ht
  have hΛp : 0 < Λ := by linarith
  have hQ1 : 1 ≤ Λ^(G+2) := hcut.1
  have hQp : 0 < Λ^(G+2) := by linarith
  have hQY : Λ^(G+2) ≤ Y := hcut.2.trans hYlo
  have hY1 : 1 ≤ Y := (Real.one_le_exp (by positivity)).trans hYlo
  obtain ⟨a,q,hq,hcop,hqlo,hqhi,happrox⟩ :=
    marked_minor_shift_reduced_approximation hQp hQY hminor ht
  have hbase := marked_minor_normalized_determinant_energy_le L T M N (θ+t/Y) a q hq hcop
    happrox hMpos hNpos hC hY1 hQ1 hqlo.le hqhi hMN hM hN c
  have hb := hrate Y hYlo hYhi
  have hB : 0 ≤ markedMinorCleanRate Y (Λ^(G+2)) C := by
    have hlog : 0 ≤ 1+Real.log (2*Y) := by
      have hh := Real.log_nonneg (show 1 ≤ 2*Y by linarith)
      linarith
    unfold markedMinorCleanRate
    positivity
  have hpow : (markedMinorCleanRate Y (Λ^(G+2)) C)^2 ≤ Λ^(-2*G) := by
    calc
      _ ≤ (Λ^(-G))^2 := pow_le_pow_left₀ hB hb 2
      _ = _ := by
        rw [← Real.rpow_mul_natCast hΛp.le]
        congr 1
        norm_num
        ring
  exact hbase.trans (mul_le_mul_of_nonneg_right hpow (by positivity))

end ArtinMatthews
