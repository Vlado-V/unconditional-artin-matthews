module

public import ArtinMatthews.SpectralKLExponentialRange
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
public import Mathlib.RingTheory.PiTensorProduct
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

/-! Exponential polynomials q(x)P(exp(-x)) lie in the actual completed
synthesis range, by the proved adjacent exponential differences. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralKLExponentialPolynomial (P : Polynomial ℂ) (x : ℝ) : ℂ :=
  (spectralKLExponentialAnchor x : ℂ)*P.eval (Real.exp (-x) : ℂ)

theorem spectralKLExponentialPolynomial_add (P Q : Polynomial ℂ) :
    spectralKLExponentialPolynomial (P+Q) = spectralKLExponentialPolynomial P+spectralKLExponentialPolynomial Q := by
  funext x
  simp only [spectralKLExponentialPolynomial,Polynomial.eval_add,mul_add,Pi.add_apply]

theorem spectralKLExponentialPolynomial_monomial (n : ℕ) (c : ℂ) :
    spectralKLExponentialPolynomial (Polynomial.monomial n c) =
      (fun x : ℝ => c*spectralKLExponentialDifference ((n : ℝ)+1) ((n : ℝ)+2) x) := by
  funext x
  unfold spectralKLExponentialPolynomial
  rw [Polynomial.eval_monomial]
  calc
    _ = c*((spectralKLExponentialAnchor x*(Real.exp (-x))^n : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul,Complex.ofReal_pow]
      ring
    _ = _ := by rw [spectralKLExponentialAnchor_monomial]

theorem spectralKLExponentialPolynomial_memLp (P : Polynomial ℂ) :
    MemLp (spectralKLExponentialPolynomial P) 2 spectralKLPhysicalMeasure := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [spectralKLExponentialPolynomial_add]
      exact hP.add hQ
  | monomial n c =>
      rw [spectralKLExponentialPolynomial_monomial]
      exact (spectralKLExponentialDifference_memLp ((n : ℝ)+1) ((n : ℝ)+2) (by have _h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith) (by have _h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)).const_smul c

def spectralKLExponentialPolynomialToLp (P : Polynomial ℂ) : Lp ℂ 2 spectralKLPhysicalMeasure :=
  (spectralKLExponentialPolynomial_memLp P).toLp (spectralKLExponentialPolynomial P)

theorem spectralKLExponentialPolynomialToLp_coe (P : Polynomial ℂ) :
    spectralKLExponentialPolynomialToLp P =ᵐ[spectralKLPhysicalMeasure] spectralKLExponentialPolynomial P :=
  MemLp.coeFn_toLp (spectralKLExponentialPolynomial_memLp P)

theorem spectralKLExponentialPolynomialToLp_add (P Q : Polynomial ℂ) :
    spectralKLExponentialPolynomialToLp (P+Q) =
      spectralKLExponentialPolynomialToLp P+spectralKLExponentialPolynomialToLp Q := by
  apply Lp.ext
  filter_upwards [spectralKLExponentialPolynomialToLp_coe (P+Q),
    Lp.coeFn_add (spectralKLExponentialPolynomialToLp P) (spectralKLExponentialPolynomialToLp Q),
    spectralKLExponentialPolynomialToLp_coe P,spectralKLExponentialPolynomialToLp_coe Q] with x hsum hadd hP hQ
  rw [hsum,hadd]
  dsimp only [Pi.add_apply]
  rw [hP,hQ]
  exact congrFun (spectralKLExponentialPolynomial_add P Q) x

theorem spectralKLExponentialPolynomialToLp_monomial (n : ℕ) (c : ℂ) :
    spectralKLExponentialPolynomialToLp (Polynomial.monomial n c) =
      c • (spectralKLExponentialDifference_memLp ((n : ℝ)+1) ((n : ℝ)+2) (by have _h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith) (by have _h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)).toLp
        (spectralKLExponentialDifference ((n : ℝ)+1) ((n : ℝ)+2)) := by
  have hE := spectralKLExponentialDifference_memLp ((n : ℝ)+1) ((n : ℝ)+2)
    (by have _h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
    (by have _h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
  apply Lp.ext
  filter_upwards [spectralKLExponentialPolynomialToLp_coe (Polynomial.monomial n c),
    Lp.coeFn_smul c (hE.toLp (spectralKLExponentialDifference ((n : ℝ)+1) ((n : ℝ)+2))),
    hE.coeFn_toLp] with x hleft hsmul hright
  rw [hleft,hsmul]
  dsimp only [Pi.smul_apply]
  rw [hright]
  exact congrFun (spectralKLExponentialPolynomial_monomial n c) x

theorem spectralKLExponentialPolynomialToLp_mem_range (P : Polynomial ℂ) :
    spectralKLExponentialPolynomialToLp P ∈ Set.range spectralKLCompletedSynthesis := by
  change spectralKLExponentialPolynomialToLp P ∈ spectralKLCompletedSynthesis.toLinearMap.range
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [spectralKLExponentialPolynomialToLp_add]
      exact spectralKLCompletedSynthesis.toLinearMap.range.add_mem hP hQ
  | monomial n c =>
      rw [spectralKLExponentialPolynomialToLp_monomial]
      exact spectralKLCompletedSynthesis.toLinearMap.range.smul_mem c
        (spectralKLExponentialDifference_mem_range ((n : ℝ)+1) ((n : ℝ)+2) (by have _h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith) (by have _h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith))

end ArtinMatthews
