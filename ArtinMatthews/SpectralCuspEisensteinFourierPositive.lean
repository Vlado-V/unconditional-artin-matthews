module

public import ArtinMatthews.SpectralCuspEisensteinFourierDirichlet


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute positive-row reindexing gives the actual nonzero Fourier
Dirichlet coefficient. All target-width factors remain explicit. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

local instance cuspFourierPositive_neZero (c : {c : ℕ // 0 < c}) : NeZero c.val :=
  ⟨c.property.ne'⟩

theorem cuspEisensteinPositiveFourier_summable (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (hs : 1 < s.re) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    Summable (fun v : CuspEisensteinPositiveRows N r a =>
      cuspEisensteinRowFourierIntegral N r a s n y hy v.val) :=
  (cuspEisensteinRowFourierIntegral_summable N r a s hs n y hy).comp_injective
    (i := fun v : CuspEisensteinPositiveRows N r a => v.val) Subtype.coe_injective

theorem cuspEisensteinCoordinateFourier_summable (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (hs : 1 < s.re) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    Summable (fun v : CuspEisensteinPositiveCoordinates N r a =>
      cuspEisensteinCoordinateFourierIntegral N r a s n y hy v.1 v.2) :=
  (cuspEisensteinPositiveCoordinateEquiv N r a).summable_iff.mpr
    (cuspEisensteinPositiveFourier_summable N r a s hs n y hy)

theorem cuspEisensteinCoordinateFourier_fibre (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (hs : 1 < s.re) (n : ℤ) (y : ℝ) (hy : 0 < y)
    (c : {c : ℕ // 0 < c}) (hD : Summable (cuspEisensteinCoordinateFourierIntegral N r a s n y hy c)) :
    (∑' d,cuspEisensteinCoordinateFourierIntegral N r a s n y hy c d) =
      gamma0TrueWidthKloostermanSum N r a c.val n 0*
        (gamma0CuspTrueWidth N r : ℂ)^(-s)*(c.val : ℂ)^(-2*s)*
        eisensteinHorizontalFourier s (n : ℝ) y := by
  let e := cuspEisensteinResidueTranslateEquiv N r a c.val c.property
  have hR : Summable (fun v : CuspEisensteinRowResidues N r a c.val × ℤ =>
      cuspEisensteinCoordinateFourierIntegral N r a s n y hy c (e v)) := e.summable_iff.mpr hD
  have hprod := Summable.tsum_prod
    (f := fun v : CuspEisensteinRowResidues N r a c.val × ℤ =>
      cuspEisensteinCoordinateFourierIntegral N r a s n y hy c (e v)) hR
  rw [← e.tsum_eq (cuspEisensteinCoordinateFourierIntegral N r a s n y hy c),hprod]
  have hOrbit (d : CuspEisensteinRowResidues N r a c.val) :
      (∑' k : ℤ,cuspEisensteinCoordinateFourierIntegral N r a s n y hy c (e (d,k))) =
      spectralRealFourierPhase (n : ℝ)
        (-(d.val.val : ℝ)/((c.val : ℝ)*(gamma0CuspTrueWidth N r : ℝ)))*
        ((gamma0CuspTrueWidth N r : ℂ)^(-s)*(c.val : ℂ)^(-2*s)*
          eisensteinHorizontalFourier s (n : ℝ) y) := by
    change (∑' k : ℤ,cuspEisensteinCoordinateFourierIntegral N r a s n y hy c
      (cuspEisensteinResidueTranslate N r a c.val (d,k))) = _
    rw [cuspEisensteinCoordinateFourierIntegral_orbit N r a s hs n y hy c d]
    ring
  simp_rw [hOrbit]
  rw [tsum_mul_right,tsum_fintype,cuspEisensteinResidueFourierSum_eq_kloosterman]
  ring

theorem cuspEisensteinPositiveFourier_dirichlet (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (hs : 1 < s.re) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    (∑' v : CuspEisensteinPositiveRows N r a,
      cuspEisensteinRowFourierIntegral N r a s n y hy v.val) =
      (gamma0CuspTrueWidth N r : ℂ)^(-s)*eisensteinHorizontalFourier s (n : ℝ) y*
        gamma0CuspFourierDirichletRaw N r a n s := by
  let f : CuspEisensteinPositiveRows N r a → ℂ :=
    fun v => cuspEisensteinRowFourierIntegral N r a s n y hy v.val
  let e := cuspEisensteinPositiveCoordinateEquiv N r a
  have hsum := cuspEisensteinCoordinateFourier_summable N r a s hs n y hy
  have hsigma := Summable.tsum_sigma
    (f := fun v : CuspEisensteinPositiveCoordinates N r a =>
      cuspEisensteinCoordinateFourierIntegral N r a s n y hy v.1 v.2) hsum
  change (∑' v,f v) = _
  rw [← e.tsum_eq f]
  change (∑' v : CuspEisensteinPositiveCoordinates N r a,
    cuspEisensteinCoordinateFourierIntegral N r a s n y hy v.1 v.2) = _
  rw [hsigma]
  have hFibre (c : {c : ℕ // 0 < c}) :
      (∑' d,cuspEisensteinCoordinateFourierIntegral N r a s n y hy c d) =
      (gamma0TrueWidthKloostermanSum N r a c.val n 0*(c.val : ℂ)^(-2*s))*
        ((gamma0CuspTrueWidth N r : ℂ)^(-s)*eisensteinHorizontalFourier s (n : ℝ) y) := by
    rw [cuspEisensteinCoordinateFourier_fibre N r a s hs n y hy c (hsum.sigma_factor c)]
    ring
  simp_rw [hFibre]
  rw [tsum_mul_right]
  change gamma0CuspFourierDirichletRaw N r a n s*
    ((gamma0CuspTrueWidth N r : ℂ)^(-s)*eisensteinHorizontalFourier s (n : ℝ) y) = _
  ring

end ArtinMatthews

