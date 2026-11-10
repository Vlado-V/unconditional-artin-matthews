module

public import ArtinMatthews.SpectralExpPolynomialDensity
public import ArtinMatthews.SpectralJRawKLCoefficientLinear
public import ArtinMatthews.SpectralJGaussianProbe
public import ArtinMatthews.SpectralWeylMultipliers
public import ArtinMatthews.SpectralJGaussianProbeKL
public import ArtinMatthews.SpectralJGaussianProbeTail
public import ArtinMatthews.SpectralJGaussianTransformLinear
public import ArtinMatthews.SpectralJNativeProfileBound
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

/-! Exact finite extension of the Gaussian calibration, with actual positive-half-line integrability. -/
namespace ArtinMatthews
open Set Filter MeasureTheory
open scoped BigOperators Polynomial
noncomputable section

private theorem native_probe_integrable (r p : ℝ) (hp : 0 < p) :
    IntegrableOn (fun x : ℝ => spectralJGaussianProbe p x * spectralWeylJMultiplier r x) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := spectralWeylJMultiplier_coordinate_bound r
  have hm : Measurable (spectralWeylJMultiplier r) :=
    spectralWeylJMultiplier_measurable.comp (measurable_const.prodMk measurable_id)
  apply ((integrable_exp_neg_mul_sq hp).integrableOn.const_mul C).mono'
    ((spectralJGaussianProbe_continuous p).measurable.mul hm).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
  have hrow : spectralJGaussianProbe p x * spectralWeylJMultiplier r x =
      ((x : ℂ) * spectralWeylJMultiplier r x) * (Real.exp (-(p * x ^ 2)) : ℂ) := by
    unfold spectralJGaussianProbe
    ring
  change ‖spectralJGaussianProbe p x * spectralWeylJMultiplier r x‖ ≤ C * Real.exp (-p * x ^ 2)
  rw [hrow, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul]
  exact mul_le_mul_of_nonneg_right (hC x (mem_Ioi.mp hx)) (Real.exp_pos _).le

theorem spectralJGaussianPolynomial_raw_coefficient (p : ℂ[X]) (r : ℝ) (hr : 0 < r) :
    let f := fun x : ℝ => (x : ℂ) * spectralExpPolynomial p (x ^ 2)
    spectralJRawKLCoefficient (spectralJGaussianTransform f) r =
      ((Real.sqrt (8 * Real.pi) : ℂ) / (4 * (Real.cosh (Real.pi * r) : ℂ))) *
        ∫ x : ℝ in Ioi 0, f x * spectralWeylJMultiplier r x := by
  let f := fun x : ℝ => (x : ℂ) * spectralExpPolynomial p (x ^ 2)
  let a (n : ℕ) := (((n + 1 : ℕ) : ℝ))
  let u (n : ℕ) := spectralJGaussianProbe (a n)
  let F (n : ℕ) := spectralJGaussianTransform (u n)
  let c := (Real.sqrt (8 * Real.pi) : ℂ) / (4 * (Real.cosh (Real.pi * r) : ℂ))
  have ha (n : ℕ) : 0 < a n := by dsimp only [a]; positivity
  have hu (n : ℕ) : IntegrableOn (u n) (Ioi (0 : ℝ)) :=
    spectralJGaussianProbe_integrable (a n) (ha n)
  have hF (n : ℕ) : Measurable (F n) :=
    (spectralJGaussianTransform_continuous (u n) (spectralJGaussianProbe_continuous (a n))
      (hu n)).measurable
  have hsum : f = fun x => ∑ n ∈ p.support, p.coeff n * u n x := by
    funext x
    simpa only [f, u, a, spectralJGaussianProbe, neg_mul] using
      spectralExpPolynomial_gaussian_sum p x
  have htf : spectralJGaussianTransform f =
      fun w => ∑ n ∈ p.support, p.coeff n * F n w := by
    rw [hsum, spectralJGaussianTransform_finsetSum p.support
      (fun n x => p.coeff n * u n x) (fun n _ => (hu n).const_mul _)]
    simp only [spectralJGaussianTransform_const_mul, F]
  have hb (n : ℕ) (w : ℝ) (hw : 2 < w) :
      ‖p.coeff n * F n w‖ ≤ (‖p.coeff n‖ * 4) / w := by
    rw [norm_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (spectralJGaussianProbe_transform_tail_bound (a n) (ha n) w (by linarith))
      (norm_nonneg _)
  have hI (n : ℕ) : IntegrableOn (fun x : ℝ => u n x * spectralWeylJMultiplier r x) (Ioi 0) :=
    native_probe_integrable r (a n) (ha n)
  have hR :
      (∫ x : ℝ in Ioi 0, f x * spectralWeylJMultiplier r x) =
        ∑ n ∈ p.support, p.coeff n * ∫ x : ℝ in Ioi 0, u n x * spectralWeylJMultiplier r x := by
    rw [hsum]
    simp only [Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum p.support (fun n _ => (hI n).const_mul (p.coeff n))]
    simp only [integral_const_mul]
  change spectralJRawKLCoefficient (spectralJGaussianTransform f) r =
    c * ∫ x : ℝ in Ioi 0, f x * spectralWeylJMultiplier r x
  rw [htf, spectralJRawKLCoefficient_finsetSum p.support
    (fun n w => p.coeff n * F n w) (fun n => ‖p.coeff n‖ * 4)
    (fun n _ => measurable_const.mul (hF n)) (fun n _ => by positivity)
    (fun n _ w hw => hb n w hw), hR, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [spectralJRawKLCoefficient_const_mul]
  change p.coeff n *
    spectralJRawKLCoefficient (spectralJGaussianTransform (spectralJGaussianProbe (a n))) r =
    c * (p.coeff n * ∫ x : ℝ in Ioi 0, u n x * spectralWeylJMultiplier r x)
  rw [spectralJRawKLCoefficient, spectralJGaussianProbe_rawKLIntegral_eq (a n) r (ha n) hr]
  dsimp only [c, u]
  ring

end
end ArtinMatthews
