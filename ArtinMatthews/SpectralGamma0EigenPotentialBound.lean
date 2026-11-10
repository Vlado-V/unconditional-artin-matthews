module

public import ArtinMatthews.SpectralGamma0EllipticPotentialCoefficient
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Fixed geometric bounds for the actual eigenvalue potential, linear in lambda. -/
noncomputable section
open Set
open scoped ContDiff
open OAI.Analysis.PDE.Weak
namespace ArtinMatthews

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)

theorem spectralEllipticPotentialFunction_linear (lam : ℝ) (x : Fin 2 → ℝ) :
    spectralEllipticPotentialFunction φ ha hφ lam x =
      lam * spectralEllipticPotentialFunction φ ha hφ 1 x := by
  let p := spectralEllipticCoordinates x
  let z := UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p)
  change (φ p * ((lam/z.im^2 : ℝ):ℂ)).re = lam*(φ p * ((1/z.im^2 : ℝ):ℂ)).re
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  ring

theorem spectralEllipticPotentialCoefficient_linear (lam : ℝ) (x : Fin 2 → ℝ) :
    spectralEllipticPotentialCoefficient φ ha hφ lam x =
      lam • spectralEllipticPotentialCoefficient φ ha hφ 1 x := by
  unfold spectralEllipticPotentialCoefficient
  rw [spectralEllipticPotentialFunction_linear φ ha hφ lam x,smul_smul]

theorem spectralEllipticPotentialCoefficient_uniform_linear_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ (lam : ℝ) (x : Fin 2 → ℝ),
      ‖spectralEllipticPotentialCoefficient φ ha hφ lam x‖ ≤ M*|lam| := by
  obtain ⟨C,hC⟩ := (spectralEllipticPotentialCoefficient_smoothBounded φ ha hφ 1).bound
  refine ⟨max C 0+1,by have := le_max_right C 0; linarith,?_⟩
  intro lam x
  rw [spectralEllipticPotentialCoefficient_linear φ ha hφ lam x,norm_smul,Real.norm_eq_abs]
  calc
    |lam| * ‖spectralEllipticPotentialCoefficient φ ha hφ 1 x‖ ≤ |lam| * (max C 0+1) :=
      mul_le_mul_of_nonneg_left ((hC x).trans (by have := le_max_left C 0; linarith))
        (abs_nonneg lam)
    _ = _ := mul_comm _ _

end ArtinMatthews
