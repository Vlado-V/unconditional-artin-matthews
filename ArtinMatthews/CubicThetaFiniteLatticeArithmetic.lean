module

public import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier
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

/-! Exact integral linear algebra on finite-adelic rational lattices. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction

variable {ι : Type*} [Fintype ι]

/-- An integral matrix acting on actual finite adele coordinates. -/
def finiteIntegerMatrixAction (M : Matrix ι ι ℤ) (x : ι → AQf) : ι → AQf :=
  fun i => ∑ j, (M i j : AQf) * x j

theorem finiteIntegerMatrixAction_integral (M : Matrix ι ι ℤ)
    {x : ι → AQf} (hx : x ∈ integralVectors) :
    finiteIntegerMatrixAction M x ∈ integralVectors := by
  intro i
  apply integralAdele.sum_mem
  intro j _
  exact integralAdele.mul_mem (intCast_mem_integralAdele _) (hx j)

theorem finiteIntegerMatrixAction_scale (M : Matrix ι ι ℤ) (r : ℚ) (x : ι → AQf) :
    finiteIntegerMatrixAction M (finiteScale r x) =
      finiteScale r (finiteIntegerMatrixAction M x) := by
  funext i
  simp only [finiteIntegerMatrixAction, finiteScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every integral matrix preserves every rationally scaled integral lattice. -/
theorem finiteIntegerMatrixAction_lattice (M : Matrix ι ι ℤ)
    (r : ℚ) (hr : r ≠ 0) {x : ι → AQf} (hx : x ∈ finiteLattice r hr) :
    finiteIntegerMatrixAction M x ∈ finiteLattice r hr := by
  rw [finiteLattice_mem_iff] at hx ⊢
  rw [← finiteIntegerMatrixAction_scale]
  exact finiteIntegerMatrixAction_integral M hx

omit [Fintype ι] in
/-- Exact change of rational lattice scale. -/
theorem finiteScale_lattice_ratio (r s : ℚ) (hr : r ≠ 0) (hs : s ≠ 0)
    {x : ι → AQf} (hx : x ∈ finiteLattice r hr) :
    finiteScale (s / r) x ∈ finiteLattice s hs := by
  rw [finiteLattice_mem_iff] at hx ⊢
  rw [finiteScale_mul]
  have h : s⁻¹ * (s / r) = r⁻¹ := by field_simp
  rw [h]
  exact hx

end ArtinMatthews
