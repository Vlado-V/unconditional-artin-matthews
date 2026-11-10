module

public import ArtinMatthews.SpectralKLSynthesis
public import ArtinMatthews.SpectralKLPoleFactor
public import ArtinMatthews.SpectralBesselProductClosed
public import ArtinMatthews.SpectralKLPoissonBilinear
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute Fubini identifies the regularized spatial synthesis pairing
with the genuine Gamma/Poisson spectral pairing. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology

namespace ArtinMatthews

theorem spectralKLSynthesisProductKernel_integral_spectral (f g : ℝ → ℂ) (ε x : ℝ) :
    (∫ p : ℝ × ℝ, spectralKLSynthesisProductKernel f g ε x p ∂volume.prod volume) =
      (x^(ε-1) : ℝ)*(spectralKLSynthesis f x*spectralKLSynthesis g x) := by
  have heq (p : ℝ × ℝ) : spectralKLSynthesisProductKernel f g ε x p =
      ((x^(ε-1) : ℝ) : ℂ)*(((spectralKLRealKernel p.1 x : ℂ)*f p.1)*
        ((spectralKLRealKernel p.2 x : ℂ)*g p.2)) := by
    unfold spectralKLSynthesisProductKernel
    ring
  simp_rw [heq]
  rw [integral_const_mul]
  rw [integral_prod_mul (μ := volume) (ν := volume)
    (fun t : ℝ => (spectralKLRealKernel t x : ℂ)*f t)
    (fun v : ℝ => (spectralKLRealKernel v x : ℂ)*g v)]
  rfl

theorem spectralKLSynthesisProductKernel_integral_spatial (f g : ℝ → ℂ)
    (ε t v : ℝ) (hε : 0 < ε) :
    (∫ x in Ioi (0 : ℝ), spectralKLSynthesisProductKernel f g ε x (t,v)) =
      f t * (spectralPoissonPeak ε (v-t) • (spectralKLRegularAmplitude t (ε,v)*g v)) := by
  have hc : (∫ x in Ioi (0 : ℝ), (x : ℂ)^((ε : ℂ)-1)*
      schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((v : ℂ)*Complex.I) x) =
      spectralPoissonPeak ε (v-t) • spectralKLRegularAmplitude t (ε,v) := by
    rw [schlafliBesselK_product_mellin_closed _ _ _ (by simpa using hε)]
    exact spectralKLRegularAmplitude_factor t ε v hε
  calc
    _ = (f t*g v)*(∫ x in Ioi (0 : ℝ), (x : ℂ)^((ε : ℂ)-1)*
        schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((v : ℂ)*Complex.I) x) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [schlafliBesselK_imaginary_eq_realKernel t hx,schlafliBesselK_imaginary_eq_realKernel v hx,
        show (ε : ℂ)-1 = ((ε-1 : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_cpow hx.le (ε-1)]
      unfold spectralKLSynthesisProductKernel
      ring
    _ = _ := by
      rw [hc,Complex.real_smul,Complex.real_smul]
      ring

theorem spectralKLSynthesis_regularized_pairing (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (ε : ℝ) (hε : 0 < ε) :
    (∫ x in Ioi (0 : ℝ), (x^(ε-1) : ℝ)*(spectralKLSynthesis f x*spectralKLSynthesis g x)) =
      ∫ t : ℝ, f t*∫ v : ℝ,
        spectralPoissonPeak ε (v-t) • (spectralKLRegularAmplitude t (ε,v)*g v) := by
  have hi := spectralKLSynthesisProductKernel_integrable f g hf hg hfc hgc ε hε
  have hs : Integrable (fun p : ℝ × ℝ => f p.1 *
      (spectralPoissonPeak ε (p.2-p.1) • (spectralKLRegularAmplitude p.1 (ε,p.2)*g p.2)))
      (volume.prod volume) := by
    convert hi.integral_prod_right using 1
    funext p
    exact (spectralKLSynthesisProductKernel_integral_spatial f g ε p.1 p.2 hε).symm
  calc
    _ = ∫ x in Ioi (0 : ℝ), ∫ p : ℝ × ℝ,
        spectralKLSynthesisProductKernel f g ε x p ∂volume.prod volume := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact (spectralKLSynthesisProductKernel_integral_spectral f g ε x).symm
    _ = ∫ p : ℝ × ℝ, (∫ x in Ioi (0 : ℝ),
        spectralKLSynthesisProductKernel f g ε x p) ∂volume.prod volume := integral_integral_swap hi
    _ = ∫ p : ℝ × ℝ, f p.1 *
        (spectralPoissonPeak ε (p.2-p.1) • (spectralKLRegularAmplitude p.1 (ε,p.2)*g p.2))
          ∂volume.prod volume := by
      apply integral_congr_ae
      filter_upwards with p
      exact spectralKLSynthesisProductKernel_integral_spatial f g ε p.1 p.2 hε
    _ = _ := by
      rw [integral_prod _ hs]
      apply integral_congr_ae
      filter_upwards with t
      exact integral_const_mul _ _

theorem spectralKLSynthesis_regularized_pairing_limit (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfp : tsupport f ⊆ Ioi (0 : ℝ)) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    Tendsto (fun ε : ℝ => ∫ x in Ioi (0 : ℝ),
      (x^(ε-1) : ℝ)*(spectralKLSynthesis f x*spectralKLSynthesis g x))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t : ℝ, ((Real.pi^2/(2*t*Real.sinh (Real.pi*t)) : ℝ) : ℂ)*(f t*g t))) := by
  apply (spectralKLRegularAmplitude_bilinear_limit f g hf hg hfc hgc hfp hgp).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (spectralKLSynthesis_regularized_pairing f g hf hg hfc hgc ε hε).symm

end ArtinMatthews
