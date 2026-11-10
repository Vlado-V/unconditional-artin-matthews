module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import ArtinMatthews.MarkedMinorArcBlockOperator
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Exact finite weighted-to-counting L2 conjugation and endpoint square-root bounds. -/
noncomputable section
namespace ArtinMatthews

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

def markedWeightedCountingVector {ι : Type*} (mass : ι → ℝ) (f : ι → ℂ) (i : ι) : ℂ :=
  (Real.sqrt (mass i):ℂ)*f i

def markedWeightedCountingMatrix {ι : Type*} (mass : ι → ℝ) (K : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => (Real.sqrt (mass i):ℂ)*K i j*(Real.sqrt (mass j):ℂ)

def markedWeightedMatrixApply {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (K : Matrix ι ι ℂ) (f : ι → ℂ) (i : ι) : ℂ :=
  ∑ j, K i j*(mass j:ℂ)*f j

theorem markedWeightedCountingVector_energy {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (hm : ∀ i, 0 ≤ mass i) (f : ι → ℂ) :
    (∑ i, ‖markedWeightedCountingVector mass f i‖^2) = ∑ i, mass i*‖f i‖^2 := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [markedWeightedCountingVector, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hm i)]

/-- The genuine weighted matrix action is conjugated to the literal matrix
with square-root mass at both endpoints. -/
theorem markedWeightedCountingMatrix_mulVec {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (hm : ∀ i, 0 ≤ mass i) (K : Matrix ι ι ℂ) (f : ι → ℂ) :
    markedWeightedCountingMatrix mass K *ᵥ markedWeightedCountingVector mass f =
      markedWeightedCountingVector mass (markedWeightedMatrixApply mass K f) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, markedWeightedCountingMatrix,
    markedWeightedCountingVector, markedWeightedMatrixApply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (Real.sqrt (mass j):ℂ)*(Real.sqrt (mass j):ℂ) = (mass j:ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (hm j)
  calc
    _ = (Real.sqrt (mass i):ℂ)*K i j*
        ((Real.sqrt (mass j):ℂ)*(Real.sqrt (mass j):ℂ))*f j := by ring
    _ = _ := by rw [hs]; ring

/-- Operator estimates in counting L2 transport to the actual finite weighted
energy without any multiplicity or cardinality loss. -/
theorem markedWeightedMatrix_energy_le_of_counting_norm {ι : Type*}
    [Fintype ι] [DecidableEq ι] (mass : ι → ℝ) (hm : ∀ i, 0 ≤ mass i)
    (K : Matrix ι ι ℂ) {C : ℝ} (hC : 0 ≤ C) (hK : ‖markedWeightedCountingMatrix mass K‖ ≤ C)
    (f : ι → ℂ) :
    (∑ i, mass i*‖markedWeightedMatrixApply mass K f i‖^2) ≤
      C^2*(∑ i, mass i*‖f i‖^2) := by
  have hh := markedMinorMatrix_energy_le_of_norm (markedWeightedCountingMatrix mass K)
    hC hK (markedWeightedCountingVector mass f)
  rw [markedWeightedCountingMatrix_mulVec mass hm K f,
    markedWeightedCountingVector_energy mass hm, markedWeightedCountingVector_energy mass hm] at hh
  exact hh

theorem markedProductMass_sqrt_endpoint_le {m C Y : ℝ} (hY : 0 < Y)
    (hm : m ≤ C/Y) : Real.sqrt (Y*m) ≤ Real.sqrt C := by
  apply Real.sqrt_le_sqrt
  have hh := (le_div_iff₀ hY).mp hm
  nlinarith

theorem markedProductMass_sqrt_pair_le {m n C Y : ℝ} (hm0 : 0 ≤ m)
    (hC : 0 ≤ C) (hY : 0 < Y) (hm : m ≤ C/Y) (hn : n ≤ C/Y) :
    Real.sqrt (m*n) ≤ C/Y := by
  rw [Real.sqrt_mul hm0]
  have hh := mul_le_mul (Real.sqrt_le_sqrt hm) (Real.sqrt_le_sqrt hn)
    (Real.sqrt_nonneg n) (Real.sqrt_nonneg (C/Y))
  simpa only [Real.mul_self_sqrt (div_nonneg hC hY.le)] using hh

end ArtinMatthews
