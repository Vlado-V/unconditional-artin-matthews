module

public import ArtinMatthews.SpectralBesselLegendreTermwise
public import ArtinMatthews.SpectralJGaussianFubini
public import ArtinMatthews.SpectralJOddSynthesis
public import ArtinMatthews.ShiftedLegendreBasis
public import ArtinMatthews.SpectralBesselLegendreGaussian
public import ArtinMatthews.SpectralJGaussianLegendreCoefficients
public import ArtinMatthews.SpectralJOddSynthesisGaussian
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace ArtinMatthews

open MeasureTheory Set
noncomputable section

/-- The Gaussian pairing of the odd synthesis is the unit-interval part of the
order-zero Bessel transform, with its exact Legendre normalization. -/
theorem spectralJOddSynthesis_gaussian_calibrated (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (p : ℝ) (hp : 1 / 4 < p) :
    (∫ x in Ioi (0 : ℝ), (Real.exp (-(p * x ^ 2)) : ℂ) * spectralJOddSynthesis f x) =
      ((1 / (4 * p) : ℝ) : ℂ) * ∫ u in (0 : ℝ)..1,
        (Real.exp (-u / (4 * p)) : ℂ) * spectralJGaussianTransform f (2 * u) := by
  let F : ℝ → ℂ := fun u => spectralJGaussianTransform f (2 * u)
  let G : ℝ → ℂ := fun u => (Real.exp (-u / (4 * p)) : ℂ)
  let C : ℂ := ((1 / (4 * p) : ℝ) : ℂ)
  have hfi : IntegrableOn f (Ioi (0 : ℝ)) :=
    (hf.integrable_of_hasCompactSupport hc).integrableOn
  have hF : Continuous F :=
    (spectralJGaussianTransform_continuous f hf hfi).comp (continuous_const.mul continuous_id)
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hcoef (n : ℕ) :
      (∫ u in (0 : ℝ)..1, (shiftedLegendreValue n u : ℂ) * F u) =
        2 * spectralJDiscreteCoefficient f (2 * n + 1) :=
    spectralJGaussianTransform_legendre_coefficient f hf hfi n
  have hpair := (shiftedLegendreInterval_bilinear_hasSum hG.continuousOn hF.continuousOn).mul_left C
  have hseries := spectralJOddSynthesis_gaussian_hasSum f hf hc hs p hp
  refine hseries.unique (hpair.congr_fun (fun n => ?_))
  rw [(spectral_besselJ_odd_gaussian n p (by linarith)).2, hcoef]
  simp only [spectralLegendreValue, shiftedLegendreValue, G, C]
  push_cast
  ring

end
end ArtinMatthews
