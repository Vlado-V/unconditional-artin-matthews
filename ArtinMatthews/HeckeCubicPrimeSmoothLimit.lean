module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.HeckePrimeSmoothSums
public import ArtinMatthews.HeckeCubicPrimeSmooth
public import ArtinMatthews.PrimeExtractionLogMomentDecay
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
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! The actual smooth prime remainder saves every logarithmic power for
each fixed Dirichlet character. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths Filter
open scoped ContDiff Topology Asymptotics

theorem cubicNumeratorPrimeSmooth_isLittleO (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (D : ℝ) :
    (fun x : ℝ => heckeRationalPrimeSmoothSum (cubicNumeratorHeckeCharacter A hA) χ W x 0)
      =o[atTop] (fun x : ℝ => x*(Real.log x)^(-D)) := by
  apply prime_extraction_all_log_moments_isLittleO
  intro k
  refine ⟨1, ?_⟩
  filter_upwards [cubicNumeratorPrimeSmooth_all_log A hA hnoncube W a b ha hsupp hW
    1 0 1 ((k : ℝ)-2) (by norm_num) (by norm_num),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (q : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with x hbound hq hx
  have hb := hbound q (by simpa only [Real.rpow_one] using hq) χ x
    (by simp only [Real.rpow_one, le_refl]) 0 (by simp)
  convert hb using 1
  rw [show -((k : ℝ)-2) = 2-(k : ℝ) by ring,
    Real.rpow_sub (Real.log_pos hx), Real.rpow_two, Real.rpow_natCast]
  ring

end ArtinMatthews
