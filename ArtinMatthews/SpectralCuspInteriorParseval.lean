module

public import Mathlib.Analysis.Fourier.AddCircle
public import ArtinMatthews.SpectralCuspLocalFourier
public import ArtinMatthews.SpectralCuspFourierProjection
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
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

/-! Parseval for the actual period-N interior coefficient, including its 1/N normalization. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
namespace ArtinMatthews

theorem cuspFourierPhase_eq_addCircle_fourier (N : ℝ) (_hN : 0 < N)
    (n : ℤ) (x : ℝ) :
    cuspFourierPhase N n x = fourier (-n) (x : AddCircle N) := by
  rw [fourier_coe_apply]
  unfold cuspFourierPhase cuspFourierFrequency
  congr 1
  push_cast
  ring

theorem cuspInteriorFourierCoefficient_eq_fourierCoeffOn_shift
    (N : ℝ) (hN : 0 < N) (n : ℤ) (u : ℝ × ℝ → ℂ) (y : ℝ) :
    cuspInteriorFourierCoefficient N n u y = cuspFourierPhase N n (N/2) *
      fourierCoeffOn hN (fun x => u (x+N/2,y)) n := by
  have he : fourierCoeffOn hN (fun x => u (x+N/2,y)) n =
      (N:ℂ)⁻¹*(∫ x in Ioc 0 N, cuspFourierPhase N n x*u (x+N/2,y)) := by
    rw [fourierCoeffOn_eq_integral]
    simp_rw [← cuspFourierPhase_eq_addCircle_fourier (N-0) (by simpa using hN) n]
    simp only [sub_zero]
    rw [intervalIntegral.integral_of_le hN.le]
    simp only [Complex.real_smul,one_div,smul_eq_mul,Complex.ofReal_inv]
  unfold cuspInteriorFourierCoefficient cuspHorizontalWeightedMean cuspHorizontalMean
  rw [he]

theorem cuspInteriorFourierCoefficient_norm_eq_fourierCoeffOn_shift
    (N : ℝ) (hN : 0 < N) (n : ℤ) (u : ℝ × ℝ → ℂ) (y : ℝ) :
    ‖cuspInteriorFourierCoefficient N n u y‖ =
      ‖fourierCoeffOn hN (fun x => u (x+N/2,y)) n‖ := by
  rw [cuspInteriorFourierCoefficient_eq_fourierCoeffOn_shift N hN,norm_mul,
    cuspFourierPhase_norm,one_mul]

theorem cuspInteriorFourierCoefficient_hasSum_sq
    (N : ℝ) (hN : 0 < N) (u : ℝ × ℝ → ℂ) (y : ℝ)
    (hL2 : MemLp (fun x => u (x+N/2,y)) 2 (volume.restrict (Ioc 0 N))) :
    HasSum (fun n : ℤ => ‖cuspInteriorFourierCoefficient N n u y‖^2)
      (N⁻¹*(∫ x in (0:ℝ)..N, ‖u (x+N/2,y)‖^2)) := by
  have he := hasSum_sq_fourierCoeffOn hN hL2
  simpa only [cuspInteriorFourierCoefficient_norm_eq_fourierCoeffOn_shift N hN,
    sub_zero,smul_eq_mul] using he

theorem cuspInteriorFourierCoefficient_frequency_window_bound
    (N : ℝ) (hN : 0 < N) (u : ℝ × ℝ → ℂ) (y : ℝ)
    (hL2 : MemLp (fun x => u (x+N/2,y)) 2 (volume.restrict (Ioc 0 N))) (s : Finset ℤ) :
    (∑ n ∈ s, ‖cuspInteriorFourierCoefficient N n u y‖^2) ≤
      N⁻¹*(∫ x in (0:ℝ)..N, ‖u (x+N/2,y)‖^2) := by
  have h := cuspInteriorFourierCoefficient_hasSum_sq N hN u y hL2
  exact (h.summable.sum_le_tsum s (fun _ _ => sq_nonneg _)).trans_eq h.tsum_eq

theorem cuspInterior_shift_slice_memLp
    (N Y : ℝ) (hN : 0 < N) (u : ℝ × ℝ → ℂ)
    (hu : ContDiffOn ℝ ∞ u (spectralOpenTwoCell N Y)) (y : ℝ) (hy : Y < y) :
    MemLp (fun x => u (x+N/2,y)) 2 (volume.restrict (Ioc 0 N)) := by
  obtain ⟨G,hG,he⟩ := spectralLocalTwoCell_smooth_extension N Y y hN hy u hu
  have hGc : Continuous (fun x : ℝ => G (x+N/2,y)) :=
    hG.continuous.comp ((continuous_id.add continuous_const).prodMk continuous_const)
  have hGl2 : MemLp (fun x : ℝ => G (x+N/2,y)) 2 (volume.restrict (Ioc 0 N)) := by
    apply (memLp_two_iff_integrable_sq_norm hGc.aestronglyMeasurable).mpr
    exact (hGc.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  apply hGl2.ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact (he (x+N/2) ⟨by linarith [hx.1],by linarith [hx.2]⟩).eq_of_nhds

end ArtinMatthews
