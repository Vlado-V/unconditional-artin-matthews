module

public import ArtinMatthews.SpectralInfinityContinuousCutoff
public import ArtinMatthews.SpectralMixedCuspContinuousDyadic
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralMixedCuspContinuousCutoff
public import ArtinMatthews.SpectralPolynomialMass
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual continuous spectral densities have an integrable quartic majorant. -/
namespace ArtinMatthews
open Set MeasureTheory
open scoped MatrixGroups BigOperators
noncomputable section

theorem gamma0ContinuousPrincipalDensity_quartic_of_cutoff
    (N : ℕ) [NeZero N] (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (C : ℝ) (hC : 0 ≤ C)
    (hcut : ∀ R : ℝ, 1 ≤ R →
      let U := (fun t : ℝ => 1 + |t|) ⁻¹' Icc 1 R
      IntegrableOn (gamma0ContinuousPrincipalDensity N b Y hY n hn) U gamma0EisensteinSpectralMeasure ∧
        (∫ t in U, gamma0ContinuousPrincipalDensity N b Y hY n hn t
          ∂gamma0EisensteinSpectralMeasure) ≤ C * R ^ 2) :
    Integrable (fun t : ℝ => gamma0ContinuousPrincipalDensity N b Y hY n hn t /
      (1 + |t|) ^ 4) gamma0EisensteinSpectralMeasure := by
  apply spectralQuadraticMass_quartic_integrable gamma0EisensteinSpectralMeasure
    (fun t : ℝ => 1 + |t|) (gamma0ContinuousPrincipalDensity N b Y hY n hn)
    (by fun_prop) (fun t => by linarith only [abs_nonneg t])
    (fun t => div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Real.cosh_pos _).le) C hC
  intro R hR
  have he : {t : ℝ | 1 + |t| ≤ R} = (fun t : ℝ => 1 + |t|) ⁻¹' Icc 1 R := by
    ext t
    simp only [mem_setOf_eq, mem_preimage, mem_Icc]
    constructor
    · intro h
      exact ⟨by linarith only [abs_nonneg t], h⟩
    · exact And.right
  rw [he]
  exact hcut R hR

theorem gamma0Infinity_continuous_quartic_integrable
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (hsmall : Y < (1 / 16) / |cuspFourierFrequency 1 n|) :
    Integrable (fun t : ℝ => gamma0ContinuousPrincipalDensity N 1 Y hY n hn t /
      (1 + |t|) ^ 4) gamma0EisensteinSpectralMeasure := by
  obtain ⟨C, hC, hBound⟩ := gamma0Infinity_continuous_packet_cutoff_bound
  let B := |cuspFourierFrequency 1 n|
  have hB : 0 < B := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)
  let D := C * (1 + B / (N : ℝ))
  apply gamma0ContinuousPrincipalDensity_quartic_of_cutoff N 1 Y hY n hn D (by dsimp only [D]; positivity)
  intro R hR
  have h := hBound N ({()} : Finset Unit) (fun _ => (1 : ℂ)) (fun _ => n)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ => hn) hR hB hY hsmall (fun _ => le_rfl)
  have hd : gamma0InfinityContinuousPacketDensity N {()} (fun _ : Unit => (1 : ℂ))
      (fun _ => n) (fun _ => hn) Y hY =
      gamma0ContinuousPrincipalDensity N 1 Y hY n hn := by
    funext t
    simp only [gamma0InfinityContinuousPacketDensity, gamma0InfinityContinuousPacketFourier,
      gamma0ContinuousPrincipalDensity, gamma0ContinuousFourierMass, Finset.sum_singleton,
      star_one, one_mul]
  rw [hd] at h
  refine ⟨h.1, h.2.trans ?_⟩
  simp only [Finset.sum_singleton, norm_one, one_pow, mul_one]
  have hq : 0 ≤ B / (N : ℝ) := by positivity
  have hR₂ : R ≤ R ^ 2 := by nlinarith only [hR]
  have hmul := mul_le_mul_of_nonneg_left hR₂ hq
  dsimp only [D]
  have hquad : R ^ 2 + B * R / (N : ℝ) ≤ (1 + B / (N : ℝ)) * R ^ 2 := by
    rw [show B * R / (N : ℝ) = (B / (N : ℝ)) * R by ring]
    nlinarith only [hmul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hquad hC.le

theorem gamma0MixedCusp_continuous_quartic_integrable
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (hsmall : Y < (1 / 16) / (|cuspFourierFrequency 1 n| /
      (gamma0CuspTrueWidth (r * s) (gamma0CuspOneOver s) : ℝ))) :
    Integrable (fun t : ℝ => gamma0ContinuousPrincipalDensity (r * s)
      (gamma0CuspOneOver s) Y hY n hn t / (1 + |t|) ^ 4) gamma0EisensteinSpectralMeasure := by
  obtain ⟨C, hC, hBound⟩ := gamma0MixedCusp_continuous_cutoff_orbit_bound
  let B := |cuspFourierFrequency 1 n|
  let D := C * (1 + B / ((r * s : ℕ) : ℝ))
  apply gamma0ContinuousPrincipalDensity_quartic_of_cutoff (r * s)
    (gamma0CuspOneOver s) Y hY n hn D (by dsimp only [D, B]; positivity)
  intro R hR
  obtain ⟨hI, hM⟩ := hBound r s hcop n hn hR hY hsmall
  refine ⟨hI, hM.trans ?_⟩
  have hq : 0 ≤ B / ((r * s : ℕ) : ℝ) := by dsimp only [B]; positivity
  have hR₂ : R ≤ R ^ 2 := by nlinarith only [hR]
  have hmul := mul_le_mul_of_nonneg_left hR₂ hq
  dsimp only [D, B]
  have hquad : R ^ 2 + B * R / ((r * s : ℕ) : ℝ) ≤
      (1 + B / ((r * s : ℕ) : ℝ)) * R ^ 2 := by
    rw [show B * R / ((r * s : ℕ) : ℝ) = (B / ((r * s : ℕ) : ℝ)) * R by ring]
    nlinarith only [hmul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hquad hC.le

end
end ArtinMatthews
