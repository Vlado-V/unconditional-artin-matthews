module

public import ArtinMatthews.SpectralGamma0LocalFourierRepresentative
public import ArtinMatthews.SpectralCuspLocalFourierODE
public import ArtinMatthews.SpectralBesselRightHalfPlane


set_option backward.privateInPublic true
@[expose] public section

/-! Application of the genuine K classification to the actual completed
cusp Fourier coefficient once its local smooth eigen-representative is given.
The mass and derivative energy conditions are derived, not assumed. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem cuspFourierFrequency_ne_zero (N : ℝ) (hN : 0 < N) (n : ℤ) (hn : n ≠ 0) :
    cuspFourierFrequency N n ≠ 0 := by
  unfold cuspFourierFrequency
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    (Int.cast_ne_zero.mpr hn)) hN.ne'

theorem gamma0CuspLocalFourier_bessel (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (v : gamma0EnergySpace N) (u : ℝ × ℝ → ℂ)
    (hu : ContDiffOn ℝ ∞ u (spectralOpenTwoCell (N : ℝ) Y))
    (hrep : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ spectralOpenTwoCell (N : ℝ) Y →
      u p = gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0EnergyInclusion N v) p)
    (hp : ∀ x t, 0 < x → x < (N : ℝ) → Y < t → u (x + N, t) = u (x, t))
    (eig : ℝ)
    (hEq : ∀ p ∈ spectralOpenTwoCell (N : ℝ) Y,
      -(p.2 ^ 2) • (spectralPlaneSecond u 0 p + spectralPlaneSecond u 1 p) = (eig : ℂ) * u p) :
    ∃ a : ℂ, ∀ y, Y < y → cuspInteriorFourierCoefficient (N : ℝ) n u y =
      a * ((Real.sqrt y : ℂ) * OAI.CubicEisenstein.schlafliBesselK
        (Complex.sqrt (1 / 4 - (eig : ℂ))) (|cuspFourierFrequency (N : ℝ) n| * y)) := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hq : 0 < |cuspFourierFrequency (N : ℝ) n| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero (N : ℝ) hN n hn)
  have hq2 : ((|cuspFourierFrequency (N : ℝ) n| : ℝ) : ℂ) ^ 2 =
      ((cuspFourierFrequency (N : ℝ) n : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast sq_abs (cuspFourierFrequency (N : ℝ) n)
  have he := gamma0CuspLocalFourierRepresentative_energy N r Y hY n v u hu hrep
  apply spectralNormalODE_classification (eig : ℂ) |cuspFourierFrequency (N : ℝ) n| Y hq hY.le
    (cuspInteriorFourierCoefficient (N : ℝ) n u)
  · exact cuspInteriorFourierCoefficient_hasDerivAt (N : ℝ) Y hN hY.le n u hu
  · intro y hy
    rw [hq2]
    exact cuspInteriorFourierCoefficient_deriv_normal_hasDerivAt (N : ℝ) Y hN hY.le n u hu hp eig hEq y hy
  · exact he.2
  · exact he.1

theorem gamma0CuspLocalFourier_bessel_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (v : gamma0EnergySpace N) (u : ℝ × ℝ → ℂ)
    (hu : ContDiffOn ℝ ∞ u (spectralOpenTwoCell (N : ℝ) Y))
    (hrep : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ spectralOpenTwoCell (N : ℝ) Y →
      u p = gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0EnergyInclusion N v) p)
    (hp : ∀ x t, 0 < x → x < (N : ℝ) → Y < t → u (x + N, t) = u (x, t))
    (eig : ℝ)
    (hEq : ∀ p ∈ spectralOpenTwoCell (N : ℝ) Y,
      -(p.2 ^ 2) • (spectralPlaneSecond u 0 p + spectralPlaneSecond u 1 p) = (eig : ℂ) * u p) :
    ∃ a : ℂ, gamma0CuspFourierCoefficient N r Y hY n (gamma0EnergyInclusion N v)
      =ᵐ[volume.restrict (Ioi Y)] fun y => a * ((Real.sqrt y : ℂ) *
        OAI.CubicEisenstein.schlafliBesselK (Complex.sqrt (1 / 4 - (eig : ℂ)))
          (|cuspFourierFrequency (N : ℝ) n| * y)) := by
  obtain ⟨a,ha⟩ := gamma0CuspLocalFourier_bessel N r Y hY n hn v u hu hrep hp eig hEq
  refine ⟨a, (gamma0CuspLocalFourierRepresentative_ae N r Y hY n
    (gamma0EnergyInclusion N v) u hrep).trans ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact ha y hy

end ArtinMatthews
