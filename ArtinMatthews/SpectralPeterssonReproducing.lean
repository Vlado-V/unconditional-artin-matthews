module

public import ArtinMatthews.SpectralPeterssonStripIntegrable
public import ArtinMatthews.SpectralPeterssonFourierAtHeight
public import ArtinMatthews.SpectralPeterssonMass


set_option backward.privateInPublic true
@[expose] public section

/-! Reproduction against the actual cusp seed with its exact Gamma mass. -/

noncomputable section
open MeasureTheory Set Matrix UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

namespace ArtinMatthews

theorem spectralPetersson_conj_seed (n : ℕ+) (z : UpperHalfPlane) :
    conj (spectralHolomorphicCuspSeed (n : ℕ) z) =
      (Real.exp (-(4*Real.pi*(n : ℝ)*z.im)) : ℂ)*spectralPeterssonFourierWeight n z := by
  unfold spectralHolomorphicCuspSeed spectralPeterssonFourierWeight
  rw [← Complex.exp_conj,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im] <;> ring

theorem spectralPeterssonCoordinatePoint_height (x y : ℝ) (hy : 0 < y) :
    spectralPeterssonCoordinatePoint (x,y) = spectralPeterssonHeightPoint x y hy := by
  apply UpperHalfPlane.ext
  unfold spectralPeterssonCoordinatePoint
  rw [ofComplex_apply_of_im_pos (by simp [hy]),spectralPeterssonHeightPoint_coe]

theorem spectralPeterssonStripCoordinate_slice (k : ℕ) (hk : 2 ≤ k) (n : ℕ+)
    (F : UpperHalfPlane → ℂ) (y : ℝ) (hy : 0 < y) :
    (∫ x in Ioc (0 : ℝ) 1, (y^2)⁻¹ • spectralPeterssonStripCoordinates k n F (x,y)) =
      ((y^(k-2)*Real.exp (-(4*Real.pi*(n : ℝ)*y)) : ℝ) : ℂ)*
        spectralPeterssonFourierAtHeight F n y hy := by
  let w := ((y^(k-2)*Real.exp (-(4*Real.pi*(n : ℝ)*y)) : ℝ) : ℂ)
  let z (x : ℝ) := spectralPeterssonHeightPoint x y hy
  change _ = w*_
  rw [spectralPeterssonFourierAtHeight,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  dsimp only
  unfold spectralPeterssonStripCoordinates UpperHalfPlane.petersson
  rw [spectralPeterssonCoordinatePoint_height x y hy,spectralPetersson_conj_seed,
    RCLike.real_smul_eq_coe_mul,zpow_natCast]
  have hpow : ((y^2)⁻¹ : ℝ) * y^k = y^(k-2) := by
    calc
      (y^2)⁻¹*y^k = (y^2)⁻¹*(y^(k-2)*y^2) := by rw [← pow_add,Nat.sub_add_cancel hk]
      _ = y^(k-2) := by field_simp
  have hpowC : (((y^2)⁻¹ : ℝ) : ℂ)*(y : ℂ)^k = (y^(k-2) : ℝ) := by exact_mod_cast hpow
  change (((y^2)⁻¹ : ℝ) : ℂ)*
    ((Real.exp (-(4*Real.pi*(n : ℝ)*y)) : ℂ)*spectralPeterssonFourierWeight n (z x)*
      F (z x)*(y : ℂ)^k) = w*(F (z x)*spectralPeterssonFourierWeight n (z x))
  calc
    _ = ((((y^2)⁻¹ : ℝ) : ℂ)*(y : ℂ)^k)*
      ((Real.exp (-(4*Real.pi*(n : ℝ)*y)) : ℂ)*F (z x)*spectralPeterssonFourierWeight n (z x)) := by ring
    _ = _ := by rw [hpowC]; unfold w; push_cast; ring

theorem spectralPeterssonStrip_reproduce (k : ℕ) (hk : 3 ≤ k) (n : ℕ+)
    (F : UpperHalfPlane → ℂ) (hF : Continuous F) (M : ℝ)
    (hbd : ∀ z, ‖F z‖*z.im^((k : ℝ)/2) ≤ M) (A : ℂ)
    (hA : ∀ (y : ℝ) (hy : 0 < y), spectralPeterssonFourierAtHeight F n y hy = A) :
    (∫ z, spectralPeterssonStripIntegrand k n F z) = (spectralPeterssonReproducingMass k n : ℂ)*A := by
  let S := (Ioc (0 : ℝ) 1) ×ˢ (Ioi (0 : ℝ))
  let G := spectralPeterssonStripCoordinates k n F
  let I (p : ℝ × ℝ) := (p.2^2)⁻¹ • G p
  have hS : MeasurableSet S := measurableSet_Ioc.prod measurableSet_Ioi
  have hpos : S ⊆ {p : ℝ × ℝ | 0 < p.2} := fun _ hp => hp.2
  have he : spectralPeterssonStripIntegrand k n F =
      {z : UpperHalfPlane | (z.re,z.im) ∈ S}.indicator (fun z => G (z.re,z.im)) := by
    funext z
    unfold spectralPeterssonStripIntegrand
    have hmem : z ∈ hyperbolicCuspStrip 1 0 ↔ (z.re,z.im) ∈ S := Iff.rfl
    by_cases hz : (z.re,z.im) ∈ S
    · have hz' : z ∈ {z : UpperHalfPlane | (z.re,z.im) ∈ S} := hz
      rw [indicator_of_mem (hmem.mpr hz),indicator_of_mem hz']
      simp only [G,spectralPeterssonStripCoordinates,spectralPeterssonCoordinatePoint_at]
    · have hz' : z ∉ {z : UpperHalfPlane | (z.re,z.im) ∈ S} := hz
      rw [indicator_of_notMem (fun h => hz (hmem.mp h)),indicator_of_notMem hz']
  have hpre : MeasurableSet {z : UpperHalfPlane | (z.re,z.im) ∈ S} := hS.preimage (by fun_prop)
  have hInt : IntegrableOn I S (volume.prod volume) :=
    spectralPeterssonStripCoordinates_weighted_integrable k hk n F hF M hbd
  rw [he,integral_indicator hpre,upperHalfPlane_setIntegral_coordinates_smul G hS hpos]
  change (∫ p in S, I p ∂(volume.prod volume)) = _
  rw [← Measure.prod_restrict]
  have hInt' : Integrable I ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [Measure.prod_restrict]
    exact hInt
  rw [integral_prod_symm I hInt']
  calc
    _ = ∫ y in Ioi (0 : ℝ), ((y^(k-2)*Real.exp (-(4*Real.pi*(n : ℝ)*y)) : ℝ) : ℂ)*A := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact (spectralPeterssonStripCoordinate_slice k (by omega) n F y hy).trans (by rw [hA y hy])
    _ = _ := by
      rw [integral_mul_const]
      congr 1
      calc
        _ = (((∫ y in Ioi (0 : ℝ), y^(k-2)*Real.exp (-(4*Real.pi*(n : ℝ)*y))) : ℝ) : ℂ) :=
          integral_complex_ofReal
        _ = _ := congrArg Complex.ofReal (spectralPeterssonReproducingMass_integral k (by omega) n)

theorem gamma0PeterssonInner_reproduce (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (hEven : Even k) (n : ℕ+) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, spectralHolomorphicSlash k (atkinRealMap γ.val) F = F)
    (hCont : Continuous (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F)) (M : ℝ)
    (hbd : ∀ z, ‖spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F z‖*z.im^((k : ℝ)/2) ≤ M)
    (A : ℂ) (hA : ∀ (y : ℝ) (hy : 0 < y), spectralPeterssonFourierAtHeight
      (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F) n y hy = A) :
    gamma0PeterssonInner N k (gamma0PeterssonPoincare N a k (n : ℕ)) F =
      (spectralPeterssonReproducingMass k n : ℂ)*A := by
  rw [gamma0PeterssonInner_unfold N a k hk hEven n F hF
    (spectralPeterssonStripIntegrand_integrable k hk n _ hCont M hbd)]
  exact spectralPeterssonStrip_reproduce k hk n _ hCont M hbd A hA

end ArtinMatthews
