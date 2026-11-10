module

public import ArtinMatthews.HeckeDirichletTwist
public import OAI.NumberTheory.DirichletL.Hecke.PrimeAnnular
public import ArtinMatthews.HeckeRationalPrimeExtraction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The literal rational prime sum with phase p^(it), matched to the
normalization of the checked Hecke prime polynomial. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths ConcretePrimeRowBridge
open scoped BigOperators Classical

def heckeRationalPrimeSum (η : HeckeFamily.Character) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℝ → ℂ) (N : ℕ) (D t : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
    idealThetaCoeff η p*χ p*W ((p : ℝ)/D)*(p : ℂ)^((t : ℂ)*Complex.I)

theorem heckeRationalPrimeSum_centered (η : HeckeFamily.Character) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℝ → ℂ) (N : ℕ) (D t : ℝ) (hD : 0 < D) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      idealThetaCoeff η p*χ p*
        (W ((p : ℝ)/D)*(((p : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift 0 t))) =
      (D : ℂ)^(-((t : ℂ)*Complex.I))*heckeRationalPrimeSum η χ W N D t := by
  have hs : -HeckeDyadic.shift 0 t = (t : ℂ)*Complex.I := by
    simp only [HeckeDyadic.shift, Complex.ofReal_zero, zero_sub, neg_neg]
  rw [hs, heckeRationalPrimeSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg p) hD.le,
    Complex.cpow_neg]
  push_cast
  ring

theorem heckeRationalPrimeSum_normalization (η : HeckeFamily.Character) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℝ → ℂ) (N : ℕ) (D t : ℝ) (hD : 0 < D) :
    ‖(D : ℂ)^(-(1/2 : ℂ)) *
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        idealThetaCoeff η p*χ p*
          (W ((p : ℝ)/D)*(((p : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift 0 t)))‖ =
      D^(-(1/2 : ℝ))*‖heckeRationalPrimeSum η χ W N D t‖ := by
  rw [heckeRationalPrimeSum_centered η χ W N D t hD, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hD, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  norm_num

theorem heckeRationalPrimeSum_le_primePolynomial (η : HeckeFamily.Character)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (W : ℝ → ℂ)
    (b D t B : ℝ) (hD : 0 < D) (hB : 0 ≤ B) (hW : ∀ y, ‖W y‖ ≤ B) :
    D^(-(1/2 : ℝ))*‖heckeRationalPrimeSum η χ W ⌊max 1 b*D⌋₊ D t‖ ≤
      ‖HeckePrimeAnnular.primePolynomial (heckeDirichletTwist η χ) W b D 0 t‖ +
        D^(-(1/2 : ℝ))*(3*(Nat.sqrt ⌊max 1 b*D⌋₊ : ℝ)*B) := by
  let N := ⌊max 1 b*D⌋₊
  let w : ℕ → ℂ := fun n =>
    W ((n : ℝ)/D)*(((n : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift 0 t)
  have hw : ∀ n ∈ Finset.Icc 1 N, ‖w n‖ ≤ B := by
    intro n hn
    have hnpos : 0 < (n : ℝ)/D := div_pos (by exact_mod_cast (Finset.mem_Icc.mp hn).1) hD
    rw [show w n = W ((n : ℝ)/D)*(((n : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift 0 t) from rfl,
      norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    simpa only [Complex.neg_re, HeckeDyadic.shift_re, neg_zero, Real.rpow_zero, mul_one] using hW ((n : ℝ)/D)
  have he := heckeDirichletPrimeSum_error η χ N w B hB hw
  have hc : ‖(D : ℂ)^(-(1/2 : ℂ))‖ = D^(-(1/2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]
    norm_num
  have he' : ‖HeckePrimeAnnular.primePolynomial (heckeDirichletTwist η χ) W b D 0 t -
      (D : ℂ)^(-(1/2 : ℂ)) *
        (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealThetaCoeff η p*χ p*w p)‖ ≤
      D^(-(1/2 : ℝ))*(3*(Nat.sqrt N : ℝ)*B) := by
    change ‖(D : ℂ)^(-(1/2 : ℂ)) *
        (∑ P ∈ (idealsUpTo N).filter Prime, thetaIdealCharacter (heckeDirichletTwist η χ) P*w P.absNorm) -
      (D : ℂ)^(-(1/2 : ℂ)) *
        (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealThetaCoeff η p*χ p*w p)‖ ≤ _
    rw [← mul_sub, norm_mul, hc]
    exact mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hD.le _)
  rw [← heckeRationalPrimeSum_normalization η χ W N D t hD]
  rw [norm_sub_rev] at he'
  exact (norm_le_insert' _
    (HeckePrimeAnnular.primePolynomial (heckeDirichletTwist η χ) W b D 0 t)).trans
      (add_le_add le_rfl he')

end ArtinMatthews
