module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.Classical.Divergence
public import OAI.Analysis.PDE.Weak.Elliptic.H1
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
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
public import Mathlib.Order.CompletePartialOrder
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
public import OAI.Analysis.PDE.Variational.LocalizedEquation
public import OAI.Analysis.PDE.Weak.Elliptic.Classical.Gradient


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem contDiff_one_cellGradient {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hu : ContDiff ℝ 2 u) : ContDiff ℝ 1 (OAI.Analysis.PDE.Variational.cellGradient u) := by
  apply (contDiff_piLp 2).mpr
  intro i
  change ContDiff ℝ 1 (fun x ↦ fderiv ℝ u x (Pi.single i 1))
  exact (hu.fderiv_right (by norm_num)).clm_apply contDiff_const

/-- The C² representative of a genuine H¹ weak solution satisfies the
classical elliptic equation at every point, with its actual classical gradient. -/
theorem classical_equation_of_H1_representative
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) (hA : ContDiff ℝ 1 A)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : Continuous g)
    (hfg : ∀ᵐ x ∂volume, x ∈ Ω → f x = g x)
    (he : WeakDivergenceEquation Ω (fun y ↦ A y (p.2 y)) f)
    (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hu : ContDiff ℝ 2 u)
    (hpu : ∀ᵐ x ∂volume, x ∈ Ω → p.1 x = u x) :
    (∀ᵐ x ∂volume, x ∈ Ω → p.2 x = OAI.Analysis.PDE.Variational.cellGradient u x) ∧
      ∀ x ∈ Ω, -classicalDivergence (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient u y)) x = g x := by
  have hgrad := OAI.Analysis.PDE.Weak.H1Zero.gradient_eq_of_value_eq hΩ hp u (hu.of_le (by norm_num)) hpu
  refine ⟨hgrad, ?_⟩
  have he' : WeakDivergenceEquation Ω (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient u y)) g := by
    apply OAI.Analysis.PDE.Variational.weakEquation_congr_on he (subset_refl _)
    · filter_upwards [hgrad] with x hx
      intro hxs
      rw [hx hxs]
    · filter_upwards [hfg] with x hx
      exact fun hxs ↦ (hx hxs).symm
  exact he'.classical_eq hΩ (hA.clm_apply (contDiff_one_cellGradient hu)) hg

end OAI.Analysis.PDE.Weak
