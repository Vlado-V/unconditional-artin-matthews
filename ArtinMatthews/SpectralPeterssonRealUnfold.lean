module

public import ArtinMatthews.SpectralPeterssonRegionUnfolding


set_option backward.privateInPublic true
@[expose] public section

/-! Real-valued periodization keeps the actual central covering factor. -/
noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem gamma0PeterssonRegion_real_integral_unfold (N : ℕ) (F : UpperHalfPlane → ℝ)
    (hF : Integrable F) :
    (∫ z in gamma0InteriorRegion N, ∑' γ : CongruenceSubgroup.Gamma0 N, F (γ.val⁻¹ • z)) =
      2*(∫ z, F z) := by
  have h := gamma0PeterssonRegion_integral_unfold N (fun z => (F z : ℂ)) hF.ofReal
  have he (z : UpperHalfPlane) :
      (∑' γ : CongruenceSubgroup.Gamma0 N, (F (γ.val⁻¹ • z) : ℂ)) =
        ((∑' γ : CongruenceSubgroup.Gamma0 N, F (γ.val⁻¹ • z) : ℝ) : ℂ) :=
    (Complex.ofReal_tsum _).symm
  simp_rw [he] at h
  rw [integral_complex_ofReal,integral_complex_ofReal] at h
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using h)

end ArtinMatthews
