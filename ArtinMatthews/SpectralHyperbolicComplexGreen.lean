module

public import ArtinMatthews.SpectralSectionWeakPairing
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import ArtinMatthews.SpectralComplexLocalGreen
public import ArtinMatthews.SpectralHyperbolicBochnerCoordinates
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual two-dimensional complex Green identity, including the
positive hyperbolic differential operator -y²(∂x²+∂y²). -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace

namespace ArtinMatthews

def spectralPlaneSecond (φ : ℝ × ℝ → ℂ) (i : Fin 2) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ (fun q => fderiv ℝ φ q (spectralPlaneDirection i)) p (spectralPlaneDirection i)

def spectralPlanePositiveSecond (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  -(∑ i : Fin 2, spectralPlaneSecond φ i p)

def spectralPlanePositiveHyperbolic (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  p.2^2 • spectralPlanePositiveSecond φ p

private theorem compact_inner_integrable (f g : ℝ × ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hs : HasCompactSupport f) :
    Integrable (fun p => inner ℂ (f p) (g p)) := by
  apply (hf.inner hg).integrable_of_hasCompactSupport
  apply hs.mono'
  intro p hp
  by_contra hout
  have hz : f p = 0 := image_eq_zero_of_notMem_tsupport hout
  exact hp (by change inner ℂ (f p) (g p) = 0; rw [hz,inner_zero_left])

theorem spectralPlaneSecond_contDiff (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (i : Fin 2) : ContDiff ℝ ∞ (spectralPlaneSecond φ i) := by
  have hd : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p (spectralPlaneDirection i)) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  exact (hd.fderiv_right (by simp)).clm_apply contDiff_const

theorem spectralPlaneSecond_compact (φ : ℝ × ℝ → ℂ)
    (hs : HasCompactSupport φ) (i : Fin 2) : HasCompactSupport (spectralPlaneSecond φ i) :=
  (hs.fderiv_apply ℝ (spectralPlaneDirection i)).fderiv_apply ℝ (spectralPlaneDirection i)

theorem spectral_plane_complex_green (φ F : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport φ) :
    (∫ p, inner ℂ (spectralPlanePositiveSecond φ p) (F p)) =
      ∫ p, ∑ i : Fin 2, inner ℂ (fderiv ℝ φ p (spectralPlaneDirection i))
        (fderiv ℝ F p (spectralPlaneDirection i)) := by
  have hfirst (i : Fin 2) : Integrable (fun p =>
      inner ℂ (fderiv ℝ φ p (spectralPlaneDirection i))
        (fderiv ℝ F p (spectralPlaneDirection i))) :=
    compact_inner_integrable _ _
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hs.fderiv_apply ℝ (spectralPlaneDirection i))
  have hsecond (i : Fin 2) : Integrable (fun p =>
      inner ℂ (-spectralPlaneSecond φ i p) (F p)) :=
    compact_inner_integrable _ _ (spectralPlaneSecond_contDiff φ hφ i).continuous.neg
      hF.continuous (spectralPlaneSecond_compact φ hs i).neg
  have he (p : ℝ × ℝ) : inner ℂ (spectralPlanePositiveSecond φ p) (F p) =
      ∑ i : Fin 2, inner ℂ (-spectralPlaneSecond φ i p) (F p) := by
    unfold spectralPlanePositiveSecond
    rw [← Finset.sum_neg_distrib,sum_inner]
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => hsecond i),integral_finsetSum _ (fun i _ => hfirst i)]
  apply Finset.sum_congr rfl
  intro i _
  exact (spectral_plane_complex_green_direction φ F hφ hF hs (spectralPlaneDirection i)).symm

/-- The actual positive hyperbolic differential operator has the complex
Dirichlet form on genuine compact tests; no form identity is postulated. -/
theorem h2_plane_complex_green (φ F : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport φ)
    (hpositive : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    (∫ z : UpperHalfPlane, inner ℂ (spectralPlanePositiveHyperbolic φ (z.re,z.im))
      (F (z.re,z.im))) =
      ∫ p, ∑ i : Fin 2, inner ℂ (fderiv ℝ φ p (spectralPlaneDirection i))
        (fderiv ℝ F p (spectralPlaneDirection i)) := by
  have hzero {p : ℝ × ℝ} (hp : ¬ 0 < p.2) : spectralPlanePositiveSecond φ p = 0 := by
    have hd (i : Fin 2) : spectralPlaneSecond φ i p = 0 := by
      apply image_eq_zero_of_notMem_tsupport (f := spectralPlaneSecond φ i)
      intro ht
      exact hp (hpositive ((tsupport_fderiv_apply_subset ℝ (spectralPlaneDirection i))
        ((tsupport_fderiv_apply_subset ℝ (spectralPlaneDirection i)) ht)))
    simp only [spectralPlanePositiveSecond,hd,Finset.sum_const_zero,neg_zero]
  have he (z : UpperHalfPlane) :
      inner ℂ (spectralPlanePositiveHyperbolic φ (z.re,z.im)) (F (z.re,z.im)) =
        z.im^2 • inner ℂ (spectralPlanePositiveSecond φ (z.re,z.im)) (F (z.re,z.im)) := by
    exact inner_smul_left_eq_smul _ _ _
  simp_rw [he]
  rw [upperHalfPlane_integral_height_sq
    (fun p => inner ℂ (spectralPlanePositiveSecond φ p) (F p))
    (fun p hp => by rw [hzero hp,inner_zero_left])]
  exact spectral_plane_complex_green φ F hφ hF hs

end ArtinMatthews
