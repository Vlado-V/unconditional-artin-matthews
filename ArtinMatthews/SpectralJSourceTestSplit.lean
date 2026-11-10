module

public import ArtinMatthews.SpectralJRealTestParts
public import ArtinMatthews.SpectralJForwardWeylNormalization
public import ArtinMatthews.SpectralJHolomorphicCoefficient
public import ArtinMatthews.SpectralBesselJCompactOrderIntegral
public import ArtinMatthews.SpectralBesselJOrderConjugation
public import ArtinMatthews.SpectralJForwardLinearity
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
public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Complex source tests split into their two actual real-valued tests in the
continuous and discrete terms of the forward-J formula. -/
noncomputable section
open Set MeasureTheory Complex
open scoped ComplexConjugate

namespace ArtinMatthews

private theorem spectralJDiscreteCoefficient_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (n : ℕ) :
    IntegrableOn (fun x => (f x/(x : ℂ))*Complex.besselJ (n : ℂ) (x : ℂ))
      (Ioi (0 : ℝ)) := by
  convert spectralBesselJOrderTransform_integrable f hf hc hp (n : ℂ) using 1
  funext x
  ring

theorem spectralJDiscreteCoefficient_parts (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (n : ℕ) :
    spectralJDiscreteCoefficient f n = spectralJDiscreteCoefficient (spectralJRealTest f) n +
      I*spectralJDiscreteCoefficient (spectralJImagTest f) n := by
  have hr := spectralJDiscreteCoefficient_integrable _ (spectralJRealTest_continuous f hf)
    (spectralJRealTest_hasCompactSupport f hc) ((spectralJRealTest_tsupport f).trans hp) n
  have hi := spectralJDiscreteCoefficient_integrable _ (spectralJImagTest_continuous f hf)
    (spectralJImagTest_hasCompactSupport f hc) ((spectralJImagTest_tsupport f).trans hp) n
  unfold spectralJDiscreteCoefficient
  rw [← integral_const_mul,← integral_add hr (hi.const_mul I)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have h : f x = spectralJRealTest f x+I*spectralJImagTest f x :=
    congrFun (spectralJTest_parts f) x
  change (f x/(x : ℂ))*Complex.besselJ (n : ℂ) (x : ℂ) =
    (spectralJRealTest f x/(x : ℂ))*Complex.besselJ (n : ℂ) (x : ℂ) +
      I*((spectralJImagTest f x/(x : ℂ))*Complex.besselJ (n : ℂ) (x : ℂ))
  rw [h]
  ring

theorem spectralJHolomorphicCoefficient_parts (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (k : ℕ) :
    spectralJHolomorphicCoefficient f k = spectralJHolomorphicCoefficient (spectralJRealTest f) k +
      I*spectralJHolomorphicCoefficient (spectralJImagTest f) k := by
  unfold spectralJHolomorphicCoefficient
  rw [spectralJDiscreteCoefficient_parts f hf hc hp]
  ring

theorem spectralJForwardTransform_parts (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (z : ℂ) :
    spectralJForwardTransform f z = spectralJForwardTransform (spectralJRealTest f) z +
      I*spectralJForwardTransform (spectralJImagTest f) z := by
  have hr := spectralJRealTest_continuous f hf
  have hi := spectralJImagTest_continuous f hf
  have hrc := spectralJRealTest_hasCompactSupport f hc
  have hic := spectralJImagTest_hasCompactSupport f hc
  have hrp := (spectralJRealTest_tsupport f).trans hp
  have hip := (spectralJImagTest_tsupport f).trans hp
  calc
    _ = spectralJForwardTransform (spectralJRealTest f+fun x => I*spectralJImagTest f x) z :=
      congrArg (fun g => spectralJForwardTransform g z) (spectralJTest_parts f)
    _ = _ := by
      have hIc : HasCompactSupport (fun x => I*spectralJImagTest f x) := hic.mul_left
      have hIp : tsupport (fun x => I*spectralJImagTest f x) ⊆ Ioi (0 : ℝ) :=
        tsupport_mul_subset_right.trans hip
      rw [spectralJForwardTransform_add (spectralJRealTest f) (fun x => I*spectralJImagTest f x)
        hr (continuous_const.mul hi) hrc hIc hrp hIp z,spectralJForwardTransform_const_mul]

theorem spectralJForwardSpectralWeight_parts (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (z : ℂ) :
    spectralJForwardSpectralWeight f z = spectralJForwardSpectralWeight (spectralJRealTest f) z +
      I*spectralJForwardSpectralWeight (spectralJImagTest f) z := by
  simp only [spectralJForwardSpectralWeight,spectralJForwardTransform_parts f hf hc hp]
  ring

theorem spectralJDiscreteCoefficient_conj (f : ℝ → ℂ)
    (hReal : ∀ x : ℝ, conj (f x) = f x) (n : ℕ) :
    conj (spectralJDiscreteCoefficient f n) = spectralJDiscreteCoefficient f n := by
  unfold spectralJDiscreteCoefficient
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change conj ((f x/(x : ℂ))*Complex.besselJ (n : ℂ) (x : ℂ)) =
    (f x/(x : ℂ))*Complex.besselJ (n : ℂ) (x : ℂ)
  rw [map_mul,map_div₀,hReal,Complex.conj_ofReal,
    spectral_besselJ_order_conj_positive (n : ℂ) hx]
  simp

theorem spectralJHolomorphicCoefficient_even_conj (f : ℝ → ℂ)
    (hReal : ∀ x : ℝ, conj (f x) = f x) (n : ℕ) :
    conj (spectralJHolomorphicCoefficient f (2*n+2)) =
      spectralJHolomorphicCoefficient f (2*n+2) := by
  rw [spectralJHolomorphicCoefficient_even_eq]
  simp only [map_mul,map_pow,map_neg,map_one,map_div₀,Complex.conj_ofReal,
    map_natCast,spectralJDiscreteCoefficient_conj f hReal]

theorem spectralJOddSynthesis_parts (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (x : ℝ) :
    spectralJOddSynthesis f x = spectralJOddSynthesis (spectralJRealTest f) x +
      I*spectralJOddSynthesis (spectralJImagTest f) x := by
  have hr := (spectralJOddSynthesis_summable_norm _ (spectralJRealTest_continuous f hf)
    (spectralJRealTest_hasCompactSupport f hc) ((spectralJRealTest_tsupport f).trans hp) x).of_norm
  have hi := (spectralJOddSynthesis_summable_norm _ (spectralJImagTest_continuous f hf)
    (spectralJImagTest_hasCompactSupport f hc) ((spectralJImagTest_tsupport f).trans hp) x).of_norm
  have ht (n : ℕ) : spectralJOddSynthesisTerm f n x =
      spectralJOddSynthesisTerm (spectralJRealTest f) n x +
        I*spectralJOddSynthesisTerm (spectralJImagTest f) n x := by
    unfold spectralJOddSynthesisTerm
    rw [spectralJDiscreteCoefficient_parts f hf hc hp]
    ring
  unfold spectralJOddSynthesis
  simp_rw [ht]
  rw [hr.tsum_add (hi.mul_left I),tsum_mul_left]

end ArtinMatthews
