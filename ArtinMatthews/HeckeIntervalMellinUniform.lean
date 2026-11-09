module

public import ArtinMatthews.HeckeIntervalMellin
public import ArtinMatthews.HeckeIntervalTransitionBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform Mellin seminorms of the actual moving interval cutoff, with
the full transition-width dependence proved from smoothTransition. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths MeasureTheory

theorem heckeInterval_mellin_uniform (lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ Real.log 2 →
      ∀ L ∈ Set.Icc (0 : ℝ) 1, ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
      (1+|t|)^j*‖mellin (PrimeLogProfile.profile (heckeLogIntervalCutoff ε u v) L)
        ((σ : ℂ)+(t : ℂ)*Complex.I)‖ ≤ C/ε^j := by
  let J := (Set.Icc (0 : ℝ) 1) ×ˢ (Set.Icc lo hi)
  have hJ : IsCompact J := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C₀, hC₀, h0⟩ := heckeLogIntervalProfile_amplitude_derivative_L1_bound
    heckeIntervalLogFactor heckeIntervalLogFactor_smooth J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := heckeLogIntervalProfile_amplitude_derivative_L1_bound
    heckeIntervalLogFactor heckeIntervalLogFactor_smooth J hJ j
  refine ⟨(1+2*Real.pi)^j*(2 : ℝ)^j*(C₀+Cj/(2*Real.pi)^j), by positivity, ?_⟩
  intro ε hε hε1 u v hu huv hv L hL σ hσ t
  have hzero : (∫ s : ℝ, ‖heckeIntervalLogFamily ε u v (L,σ) s‖) ≤ C₀ := by
    simpa only [iteratedDeriv_zero, pow_zero, div_one, heckeIntervalLogFamily] using
      h0 (L,σ) ⟨hL,hσ⟩ ε hε hε1 u v hu huv hv
  have hderiv : (∫ s : ℝ, ‖iteratedDeriv j (heckeIntervalLogFamily ε u v (L,σ)) s‖) ≤ Cj/ε^j :=
    hj (L,σ) ⟨hL,hσ⟩ ε hε hε1 u v hu huv hv
  have hC0 : C₀ ≤ C₀/ε^j := by
    apply (le_div_iff₀ (pow_pos hε j)).mpr
    exact mul_le_of_le_one_right hC₀.le (pow_le_one₀ hε.le hε1)
  apply (heckeInterval_mellin_derivative_bound hε huv L σ t j).trans
  calc
    _ ≤ (1+2*Real.pi)^j*(2 : ℝ)^j*(C₀/ε^j+(Cj/ε^j)/(2*Real.pi)^j) := by
      gcongr
      exact hzero.trans hC0
    _ = _ := by ring

end ArtinMatthews
