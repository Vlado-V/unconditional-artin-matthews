module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.Henselian
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
public import OAI.NumberTheory.DirichletL.FiniteFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Actual product characters and their Gauss sums. The nonunit mask is
proved for the full product ring, and the normalization retains every
unit-shift cross factor. No Gauss norm is supplied as a hypothesis. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
open scoped Classical BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] (R : ι → Type*) [∀ i, CommRing (R i)]

def reflectionProductCharacter (χ : ∀ i, MulChar (R i) ℂ) : MulChar (∀ i, R i) ℂ where
  toFun x := ∏ i, χ i (x i)
  map_one' := by simp
  map_mul' x y := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
  map_nonunit' x hx := by
    have he : ∃ i, ¬ IsUnit (x i) := by
      by_contra hn
      push Not at hn
      exact hx (Pi.isUnit_iff.mpr hn)
    obtain ⟨i, hi⟩ := he
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((χ i).map_nonunit hi)

def reflectionProductPhase (ψ : ∀ i, AddChar (R i) ℂ) : AddChar (∀ i, R i) ℂ where
  toFun x := ∏ i, ψ i (x i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Pi.add_apply, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

variable [∀ i, Fintype (R i)]

theorem reflectionProductGauss_eq (χ : ∀ i, MulChar (R i) ℂ)
    (ψ : ∀ i, AddChar (R i) ℂ) :
    gaussSum (reflectionProductCharacter R χ) (reflectionProductPhase R ψ) =
      ∏ i, gaussSum (χ i) (ψ i) := by
  classical
  change (∑ x : ∀ i, R i, (∏ i, χ i (x i)) * (∏ i, ψ i (x i))) = _
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (κ := R) (R := ℂ) (fun i x => χ i x * ψ i x)).symm

theorem reflectionProductGauss_unit_shift (χ : ∀ i, MulChar (R i) ℂ)
    (ψ : ∀ i, AddChar (R i) ℂ) (u : ∀ i, (R i)ˣ) :
    gaussSum (reflectionProductCharacter R χ)
      (reflectionProductPhase R (fun i => (ψ i).mulShift (u i))) =
        (∏ i, (χ i)⁻¹ (u i)) * ∏ i, gaussSum (χ i) (ψ i) := by
  rw [reflectionProductGauss_eq]
  simp_rw [gaussSum_mulShift_eq]
  exact Finset.prod_mul_distrib

section Fields
variable (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]

theorem reflectionProductGauss_norm (χ : ∀ i, MulChar (F i) ℂ)
    (hχ : ∀ i, χ i ≠ 1) (ψ : ∀ i, AddChar (F i) ℂ)
    (hψ : ∀ i, (ψ i).IsPrimitive) :
    ‖gaussSum (reflectionProductCharacter F χ) (reflectionProductPhase F ψ)‖ =
      ∏ i, Real.sqrt (Fintype.card (F i) : ℝ) := by
  rw [reflectionProductGauss_eq, norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact primitive_gaussSum_norm (χ i) (primitiveOnIdeals_of_field _ (hχ i)) (ψ i) (hψ i)

theorem reflectionProductGamma_norm (χ : ∀ i, MulChar (F i) ℂ)
    (hχ : ∀ i, χ i ≠ 1) (ψ : ∀ i, AddChar (F i) ℂ)
    (hψ : ∀ i, (ψ i).IsPrimitive) :
    ‖gaussSum (reflectionProductCharacter F χ) (reflectionProductPhase F ψ) /
      (Real.sqrt (Fintype.card (∀ i, F i) : ℝ) : ℂ)‖ = 1 := by
  have hc : Real.sqrt (Fintype.card (∀ i, F i) : ℝ) =
      ∏ i, Real.sqrt (Fintype.card (F i) : ℝ) := by
    rw [Fintype.card_pi, Nat.cast_prod, Real.sqrt_prod]
    intro i _
    exact Nat.cast_nonneg _
  have hp : 0 < ∏ i, Real.sqrt (Fintype.card (F i) : ℝ) := by
    apply Finset.prod_pos
    intro i _
    exact Real.sqrt_pos.2 (by exact_mod_cast (Fintype.card_pos (α := F i)))
  rw [norm_div, reflectionProductGauss_norm F χ hχ ψ hψ, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), hc, div_self hp.ne']

end Fields
end
end ArtinMatthews.VaryingKummerAnalytic
