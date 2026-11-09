module

public import ArtinMatthews.SpectralInfinityHighPoincareBessel


set_option backward.privateInPublic true
@[expose] public section

/-! The real norm-square identity for the genuine cusp projection.
The complementary ambient mass occurs as its actual nonnegative
norm square, including for a compact Fourier Poincare packet. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace BigOperators

namespace ArtinMatthews

theorem gamma0_mass_spectral_normsq (N : ℕ) [NeZero N] (f : Gamma0RegionL2 N) :
    Summable (fun i : Gamma0AllHeightSpectralIndex N =>
      ‖inner ℂ f (gamma0FullCuspidalSpectralBasis N i).val‖^2) ∧
    ‖f‖^2 = (∑' i : Gamma0AllHeightSpectralIndex N,
      ‖inner ℂ f (gamma0FullCuspidalSpectralBasis N i).val‖^2) +
        ‖gamma0NoncuspidalRemainder N f‖^2 := by
  let b (i : Gamma0AllHeightSpectralIndex N) := inner ℂ f (gamma0FullCuspidalSpectralBasis N i).val
  have hterm (i : Gamma0AllHeightSpectralIndex N) :
      (b i * inner ℂ (gamma0FullCuspidalSpectralBasis N i).val f).re = ‖b i‖^2 := by
    rw [← inner_conj_symm (gamma0FullCuspidalSpectralBasis N i).val f]
    change (b i * (starRingEnd ℂ) (b i)).re = _
    rw [mul_comm,← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  have hs := Complex.reCLM.hasSum (gamma0CuspidalProjection_spectral_hasSum N f f)
  change HasSum (fun i => (b i*inner ℂ (gamma0FullCuspidalSpectralBasis N i).val f).re)
    (inner ℂ (gamma0CuspidalProjection N f) (gamma0CuspidalProjection N f)).re at hs
  simp only [hterm] at hs
  refine ⟨hs.summable,?_⟩
  rw [hs.tsum_eq,← inner_self_eq_norm_sq (𝕜 := ℂ) f,
    ← inner_self_eq_norm_sq (𝕜 := ℂ) (gamma0NoncuspidalRemainder N f)]
  change (inner ℂ f f).re = (inner ℂ (gamma0CuspidalProjection N f) (gamma0CuspidalProjection N f)).re +
    (inner ℂ (gamma0NoncuspidalRemainder N f) (gamma0NoncuspidalRemainder N f)).re
  simpa only [Complex.add_re] using congrArg Complex.re (gamma0_mass_cuspidal_split N f f)

theorem gamma0FourierPoincarePacket_spectral_normsq {ι : Type*} (N : ℕ) [NeZero N]
    (t : Finset ι) (α : ι → ℂ) (r : ι → SL(2, ℤ)) (n : ι → ℤ) (hn : ∀ j, n j ≠ 0)
    (Y : ℝ) (hY : 0 < Y) (ρ : ι → ℝ → ℝ) (hρ : ∀ j, ContDiff ℝ ∞ (ρ j))
    (hcρ : ∀ j, HasCompactSupport (ρ j)) (hpρ : ∀ j, tsupport (ρ j) ⊆ Ioi (0 : ℝ))
    (hsρ : ∀ j, tsupport (ρ j) ⊆ Ioi Y) :
    let P := gamma0FourierPoincarePacket N t α r n ρ hρ hcρ hpρ
    let C (i : Gamma0AllHeightSpectralIndex N) := ∑ j ∈ t, star (α j)*
      gamma0FourierPoincareSpectralCoefficient N i (r j) Y hY (n j) (hn j) (ρ j)
    Summable (fun i => ‖C i‖^2) ∧
      ‖P‖^2 = (∑' i : Gamma0AllHeightSpectralIndex N, ‖C i‖^2) +
        ‖gamma0NoncuspidalRemainder N P‖^2 := by
  dsimp only
  simpa only [gamma0FourierPoincarePacket_inner N _ t α r n hn Y hY ρ hρ hcρ hpρ hsρ] using
    gamma0_mass_spectral_normsq N (gamma0FourierPoincarePacket N t α r n ρ hρ hcρ hpρ)

end ArtinMatthews
