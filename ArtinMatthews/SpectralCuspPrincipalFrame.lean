module

public import ArtinMatthews.SpectralCuspPrincipalMoment
public import ArtinMatthews.SpectralKFrameFinset


set_option backward.privateInPublic true
@[expose] public section

/-! The compact K frame acts on the genuine finite cusp moment. -/
noncomputable section
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

theorem gamma0CuspPrincipalMoment_frame_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N]
      (u : Finset (Gamma0AllHeightSpectralIndex N)) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
      (n : ℤ) (hn : n ≠ 0) (T V : ℝ), 1/2 ≤ T → 0 ≤ V →
      (∀ i ∈ u, 1/4 ≤ gamma0AllHeightGradientSpectralValue N i) →
      (∀ i ∈ u, T ≤ 1+|gamma0CuspPrincipalParameter N i| ∧ 1+|gamma0CuspPrincipalParameter N i| ≤ 2*T) →
      (∀ F : ℝ → ℝ, spectralKFrameProfileBound T F →
        gamma0CuspPhysicalBesselMoment N u b Y hY n hn F ≤ V*spectralKFrameLength) →
      gamma0CuspPrincipalMoment N u b Y hY n hn ≤ C*T^2*V := by
  obtain ⟨C,hC,hFrame⟩ := spectralKFrame_principal_finset_bound
  refine ⟨C,hC,?_⟩
  intro N inst u b Y hY n hn T V hT hV hPrincipal hBand hMoment
  let A (i : Gamma0AllHeightSpectralIndex N) : ℝ := ‖gamma0CuspUnitAmplitude N i b Y hY n hn‖^2
  apply hFrame u (gamma0CuspPrincipalParameter N) A T V hT hV (fun i _ => sq_nonneg _) hBand
  intro F hF
  have h := hMoment F hF
  rw [gamma0CuspPhysicalBesselMoment_principal_eq N u b Y hY n hn F hPrincipal] at h
  exact h

end ArtinMatthews
