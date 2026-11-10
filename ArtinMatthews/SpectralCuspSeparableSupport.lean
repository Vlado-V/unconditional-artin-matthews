module

public import ArtinMatthews.SpectralRealSeparableLaplacian
public import ArtinMatthews.SpectralSectionLaplacianSeed
public import ArtinMatthews.SpectralHorizontalPeriodPartition
public import ArtinMatthews.SpectralCuspMass
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine support of the horizontal period-window tests and their actual
hyperbolic Laplacians. Flatness at the two boundary points is proved from
smoothness and the literal one-sided vanishings. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace ArtinMatthews

theorem spectral_deriv_zero_on_left {f : ℝ → ℝ} (hdf : Continuous (deriv f))
    (a : ℝ) (hf : ∀ x ≤ a, f x = 0) : ∀ x ≤ a, deriv f x = 0 := by
  have hs : Iio a ⊆ {x | deriv f x = 0} := by
    intro x hx
    have he : f =ᶠ[𝓝 x] 0 := by
      filter_upwards [isOpen_Iio.mem_nhds hx] with t ht
      exact hf t ht.le
    change deriv f x = 0
    have h := he.deriv_eq
    change deriv f x = deriv (fun _ : ℝ => (0 : ℝ)) x at h
    simpa only [deriv_const] using h
  have hc := closure_minimal hs (isClosed_eq hdf continuous_const)
  rw [closure_Iio] at hc
  exact fun x hx => hc hx

theorem spectral_deriv_zero_on_right {f : ℝ → ℝ} (hdf : Continuous (deriv f))
    (a : ℝ) (hf : ∀ x, a ≤ x → f x = 0) : ∀ x, a ≤ x → deriv f x = 0 := by
  have hs : Ioi a ⊆ {x | deriv f x = 0} := by
    intro x hx
    have he : f =ᶠ[𝓝 x] 0 := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
      exact hf t ht.le
    change deriv f x = 0
    have h := he.deriv_eq
    change deriv f x = deriv (fun _ : ℝ => (0 : ℝ)) x at h
    simpa only [deriv_const] using h
  have hc := closure_minimal hs (isClosed_eq hdf continuous_const)
  rw [closure_Ioi] at hc
  exact fun x hx => hc hx

theorem spectralHorizontalPartition_deriv2_zero_left {w x : ℝ}
    (hw : 0 < w) (hx : x ≤ 0) :
    deriv (deriv (spectralHorizontalPartition w)) x = 0 := by
  have hα := spectralHorizontalPartition_contDiff w
  have hα' := (contDiff_infty_iff_deriv.mp hα).2
  exact spectral_deriv_zero_on_left (hα'.continuous_deriv (by simp)) 0
    (spectral_deriv_zero_on_left (hα.continuous_deriv (by simp)) 0
      (fun t ht => spectralHorizontalPartition_zero_left hw ht)) x hx

theorem spectralHorizontalPartition_deriv2_zero_right {w x : ℝ}
    (hw : 0 < w) (hx : 2 * w ≤ x) :
    deriv (deriv (spectralHorizontalPartition w)) x = 0 := by
  have hα := spectralHorizontalPartition_contDiff w
  have hα' := (contDiff_infty_iff_deriv.mp hα).2
  exact spectral_deriv_zero_on_right (hα'.continuous_deriv (by simp)) (2 * w)
    (spectral_deriv_zero_on_right (hα.continuous_deriv (by simp)) (2 * w)
      (fun t ht => spectralHorizontalPartition_zero_right hw ht)) x hx

def cuspConstantTermTestSeed (w : ℝ) (hw : 0 < w) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρpos : tsupport ρ ⊆ Ioi (0 : ℝ)) : h2SmoothCompactSeeds :=
  h2RealSeparableSmoothSeed (spectralHorizontalPartition w) ρ
    (spectralHorizontalPartition_contDiff w) hρ
    (spectralHorizontalPartition_hasCompactSupport hw) hρc hρpos

theorem cuspConstantTermTestSeed_support (w : ℝ) (hw : 0 < w) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (Y : ℝ) (hs : tsupport ρ ⊆ Ioi Y) :
    Function.support (fun z : UpperHalfPlane => (cuspConstantTermTestSeed w hw ρ hρ hρc hρpos).val z)
      ⊆ hyperbolicCuspStrip (2 * w) Y := by
  intro z hz
  change (cuspConstantTermTestSeed w hw ρ hρ hρc hρpos).val z ≠ 0 at hz
  have hn : spectralHorizontalPartition w z.re * ρ z.im ≠ 0 := by
    simpa only [cuspConstantTermTestSeed, h2RealSeparableSmoothSeed_apply,
      Complex.ofReal_ne_zero] using hz
  have hα : spectralHorizontalPartition w z.re ≠ 0 := (mul_ne_zero_iff.mp hn).1
  have hρz : ρ z.im ≠ 0 := (mul_ne_zero_iff.mp hn).2
  refine ⟨⟨?_, ?_⟩, hs (subset_tsupport ρ hρz)⟩
  · by_contra h
    exact hα (spectralHorizontalPartition_zero_left hw (le_of_not_gt h))
  · exact (spectralHorizontalPartition_tsupport hw (subset_tsupport _ hα)).2

theorem cuspConstantTermTestSeed_laplacian_support (w : ℝ) (hw : 0 < w) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (Y : ℝ) (hs : tsupport ρ ⊆ Ioi Y) :
    Function.support (fun z : UpperHalfPlane =>
      (h2SectionLaplacianSeed (cuspConstantTermTestSeed w hw ρ hρ hρc hρpos)).val z)
        ⊆ hyperbolicCuspStrip (2 * w) Y := by
  intro z hz
  by_contra hnot
  have hzero : h2SectionPositiveLaplacian (cuspConstantTermTestSeed w hw ρ hρ hρc hρpos).val z = 0 := by
    rw [cuspConstantTermTestSeed, h2RealSeparableSmoothSeed_laplacian]
    by_cases hx : z.re ≤ 0
    · rw [spectralHorizontalPartition_zero_left hw hx,
        spectralHorizontalPartition_deriv2_zero_left hw hx]
      simp only [zero_mul, add_zero, mul_zero, Complex.ofReal_zero]
    by_cases hx' : 2 * w ≤ z.re
    · rw [spectralHorizontalPartition_zero_right hw hx',
        spectralHorizontalPartition_deriv2_zero_right hw hx']
      simp only [zero_mul, add_zero, mul_zero, Complex.ofReal_zero]
    have hy : ¬Y < z.im := fun hy => hnot ⟨⟨lt_of_not_ge hx, (lt_of_not_ge hx').le⟩, hy⟩
    have hρz : ρ z.im = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))
    have hρ2 : deriv (deriv ρ) z.im = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (hs (tsupport_deriv_subset (tsupport_deriv_subset h))))
    rw [hρz, hρ2]
    simp only [mul_zero, zero_add, Complex.ofReal_zero]
  exact hz hzero

end ArtinMatthews
