module

public import ArtinMatthews.SpectralPeterssonCutStripIntegrable
public import ArtinMatthews.SpectralPeterssonReproducing
public import ArtinMatthews.SpectralPeterssonTruncatedMass


set_option backward.privateInPublic true
@[expose] public section

/-! The true sharp-cut pairing reproduces the Fourier coefficient with
its incomplete-Gamma mass. The argument covers weight two directly. -/
noncomputable section
open Set MeasureTheory UpperHalfPlane
open scoped ComplexConjugate

namespace ArtinMatthews

theorem spectralPeterssonCutStrip_reproduce (k : ℕ) (hk : 2 ≤ k) (n : ℕ+)
    (A : ℝ) (hA : 0 < A) (F : UpperHalfPlane → ℂ) (hF : Continuous F) (M : ℝ)
    (hbd : ∀ z, ‖F z‖*z.im^((k : ℝ)/2) ≤ M) (b : ℂ)
    (hb : ∀ (y : ℝ) (hy : 0 < y), spectralPeterssonFourierAtHeight F n y hy = b) :
    (∫ z, UpperHalfPlane.petersson (k : ℤ) (spectralPeterssonStripCutSeed n A) F z) =
      (spectralPeterssonTruncatedMass k n A : ℂ)*b := by
  let δ := A/(4*Real.pi*(n : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let S := (Ioc (0 : ℝ) 1) ×ˢ Ioi δ
  let G := spectralPeterssonStripCoordinates k n F
  let I (p : ℝ × ℝ) := (p.2^2)⁻¹ • G p
  have hS : MeasurableSet S := measurableSet_Ioc.prod measurableSet_Ioi
  have hpos : S ⊆ {p : ℝ × ℝ | 0 < p.2} := fun _ hp => hδ.trans hp.2
  have hpre : MeasurableSet {z : UpperHalfPlane | (z.re,z.im) ∈ S} := hS.preimage (by fun_prop)
  rw [spectralPeterssonCutStrip_coordinates]
  change (∫ z, ({z : UpperHalfPlane | (z.re,z.im) ∈ S}.indicator
    (fun z : UpperHalfPlane => G (z.re,z.im))) z) = _
  rw [integral_indicator hpre,upperHalfPlane_setIntegral_coordinates_smul G hS hpos]
  have hInt : IntegrableOn I S (volume.prod volume) :=
    spectralPeterssonCutCoordinates_weighted_integrable k hk n δ hδ F hF M hbd
  change (∫ p in S, I p ∂(volume.prod volume)) = _
  rw [← Measure.prod_restrict]
  have hInt' : Integrable I ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioi δ))) := by
    rw [Measure.prod_restrict]
    exact hInt
  rw [integral_prod_symm I hInt']
  calc
    _ = ∫ y in Ioi δ, ((y^(k-2)*Real.exp (-(4*Real.pi*(n : ℝ)*y)) : ℝ) : ℂ)*b := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      have hy0 : 0 < y := hδ.trans hy
      exact (spectralPeterssonStripCoordinate_slice k hk n F y hy0).trans (by rw [hb y hy0])
    _ = _ := by
      rw [integral_mul_const,integral_complex_ofReal]
      rfl

end ArtinMatthews
