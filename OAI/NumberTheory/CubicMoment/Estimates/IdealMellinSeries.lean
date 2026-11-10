module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicMoment.Estimates.ShortMoebius
public import OAI.NumberTheory.CubicMoment.Estimates.MellinSeries
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import OAI.NumberTheory.CubicGram.EuclideanDomain
public import OAI.NumberTheory.CubicGram.IntegerBasis
public import OAI.NumberTheory.CubicMoment.Estimates.NormSeries


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Absolute convergence and Mellin inversion for the complete ideal
series. Prime-exponent vectors include all nonzero ideals, including
the ramified prime; no Euler factor is silently removed. -/

noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

private lemma idealExponentOf_one_aux : idealExponentOf 1 = 0 := by
  have h : Associates.factors' (1 : Eisenstein) = 0 := by
    apply WithTop.coe_inj.mp
    rw [← Associates.factors_mk _ one_ne_zero,Associates.mk_one,Associates.factors_one]
    rfl
  simp [idealExponentOf,h]

lemma idealExponentOf_pow {a : Eisenstein} (ha : a ≠ 0) (k : ℕ) :
    idealExponentOf (a^k) = k • idealExponentOf a := by
  induction k with
  | zero => simp [idealExponentOf_one_aux]
  | succ k ih => rw [pow_succ,idealExponentOf_mul (pow_ne_zero _ ha) ha,ih,add_nsmul,one_nsmul]

lemma idealExponentOf_primeRepresentative (p : EisensteinIdealPrime) :
    idealExponentOf (idealPrimeRepresentative p) = Finsupp.single p 1 := by
  have h : Associates.factors' (idealPrimeRepresentative p) = {p} := by
    apply WithTop.coe_inj.mp
    rw [← Associates.factors_mk _ (idealPrimeRepresentative_irreducible p).ne_zero]
    have he : Associates.mk (idealPrimeRepresentative p) = p.val := Associates.quotient_out p.val
    rw [he]
    exact Associates.factors_self p.property
  simp [idealExponentOf,h]

lemma idealExponentOf_generator (ν : EisensteinIdealExponent) :
    idealExponentOf (idealExponentGenerator ν) = ν := by
  induction ν using Finsupp.induction_linear with
  | zero => simpa [idealExponentGenerator] using idealExponentOf_one_aux
  | add ν κ hν hκ =>
      rw [idealExponentGenerator_add,idealExponentOf_mul
        (idealExponentGenerator_ne_zero ν) (idealExponentGenerator_ne_zero κ),hν,hκ]
  | single p k =>
      simp only [idealExponentGenerator,Finsupp.prod_single_index,pow_zero]
      rw [idealExponentOf_pow (idealPrimeRepresentative_irreducible p).ne_zero,
        idealExponentOf_primeRepresentative]
      simp

lemma idealExponentGenerator_injective : Function.Injective idealExponentGenerator :=
  Function.LeftInverse.injective idealExponentOf_generator

instance idealExponentCountable : Countable EisensteinIdealExponent := by
  have : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  exact idealExponentGenerator_injective.countable

theorem summable_ideal_norm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun ν : EisensteinIdealExponent => idealExponentNorm ν^(-σ)) := by
  have h := (summable_eisenstein_norm_rpow hσ).comp_injective idealExponentGenerator_injective
  simpa only [Function.comp_def,idealExponentNorm,normNat_cast] using h

theorem summable_ideal_character_weight {σ : ℝ} (hσ : 1 < σ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    Summable (fun ν => ‖χ ν‖*idealExponentNorm ν^(-σ)) := by
  apply (summable_ideal_norm_rpow hσ).of_norm_bounded
  intro ν
  have hn := idealExponentNorm_pos ν
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (by positivity) (hχ ν)

/-- The complete ideal character sum, with its full Dirichlet series,
has the Mellin representation on every line to the right of one. -/
theorem ideal_smooth_mellin (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ Z : ℝ} (hσ : 1 < σ) (hZ : 0 < Z) :
    (∑' ν, χ ν*W (idealExponentNorm ν/Z)) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W (σ+(τ:ℂ)*Complex.I) * (Z:ℂ)^(σ+(τ:ℂ)*Complex.I) *
        normDirichletSeries χ idealExponentNorm (σ+(τ:ℂ)*Complex.I) :=
  smooth_mellin_series χ idealExponentNorm idealExponentNorm_pos W hW hpos hsm σ
    (summable_ideal_character_weight hσ χ hχ) hZ

end CubicFirstMoment

end

end OAI
