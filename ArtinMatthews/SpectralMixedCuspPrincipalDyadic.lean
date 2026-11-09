module

public import ArtinMatthews.SpectralMixedCuspPhysicalOrbitMass
public import ArtinMatthews.SpectralCuspPrincipalFrame


set_option backward.privateInPublic true
@[expose] public section

/-! A level-uniform principal Bessel estimate in one dyadic band at 1/s. -/

noncomputable section
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

theorem gamma0MixedCusp_principal_dyadic_orbit_bessel :
    ∃ C : ℝ, 0 < C ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ (u : Finset (Gamma0AllHeightSpectralIndex (r*s))) (n : ℤ) (hn : n ≠ 0)
        {T Y : ℝ}, (1/2 : ℝ) ≤ T → ∀ hY : 0 < Y,
      Y < (T/16)/(|cuspFourierFrequency 1 n| /
        (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) →
      (∀ i ∈ u, 1/4 ≤ gamma0AllHeightGradientSpectralValue (r*s) i) →
      (∀ i ∈ u, T ≤ 1+|gamma0CuspPrincipalParameter (r*s) i| ∧
        1+|gamma0CuspPrincipalParameter (r*s) i| ≤ 2*T) →
      gamma0CuspPrincipalMoment (r*s) u (gamma0CuspOneOver s) Y hY n hn ≤
        C*(T^2+|cuspFourierFrequency 1 n| * T/((r*s : ℕ) : ℝ)) := by
  obtain ⟨C,hC,hFrame⟩ := gamma0CuspPrincipalMoment_frame_bound
  refine ⟨192*C,by positivity,?_⟩
  intro r s ir is hcop u n hn T Y hhalf hY hYB hPrincipal hBand
  let q := |cuspFourierFrequency 1 n|
  let V := 6*(1+2*q/(((r*s : ℕ) : ℝ)*(T/16)))
  have hT : 0 < T := by linarith
  have hN : 0 < (((r*s : ℕ) : ℝ)) := Nat.cast_pos.mpr (NeZero.pos (r*s))
  have hV : 0 ≤ V := by dsimp only [V,q]; positivity
  have h := hFrame (r*s) u (gamma0CuspOneOver s) Y hY n hn T V hhalf hV hPrincipal hBand
    (fun F hF => by
      obtain ⟨hs,hc,hS,hm⟩ := hF
      have hM := gamma0MixedCusp_physical_finite_bessel r s hcop u n hn F hs hc
        (by positivity : 0 < T/16) hY hYB hS
      exact hM.trans (mul_le_mul_of_nonneg_left hm hV))
  exact h.trans (spectral_principal_orbit_growth_le hC.le hT hN)

end ArtinMatthews
