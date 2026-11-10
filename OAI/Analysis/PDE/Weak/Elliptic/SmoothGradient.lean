module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Variational.CellL2
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import OAI.Analysis.PDE.Weak.Elliptic.TestSupport


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

theorem contDiff_cellGradient {m : ℕ} {η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hη : ContDiff ℝ ∞ η) : ContDiff ℝ ∞ (OAI.Analysis.PDE.Variational.cellGradient η) := by
  apply (contDiff_piLp 2).mpr
  intro i
  change ContDiff ℝ ∞ (fun x ↦ fderiv ℝ η x (Pi.single i 1))
  exact (hη.fderiv_right (by simp)).clm_apply contDiff_const

theorem exists_cellGradient_derivative_bound {m : ℕ} {η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hη : ContDiff ℝ ∞ η) (hs : HasCompactSupport η) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ x, ‖fderiv ℝ (OAI.Analysis.PDE.Variational.cellGradient η) x‖ ≤ J := by
  have hg := contDiff_cellGradient hη
  have hgs := hasCompactSupport_cellGradient hs
  obtain ⟨J, hJ⟩ := ((hgs.fderiv (𝕜 := ℝ)).isCompact_range
    (hg.continuous_fderiv (by simp))).isBounded.exists_norm_le
  have hJ' : ∀ x, ‖fderiv ℝ (OAI.Analysis.PDE.Variational.cellGradient η) x‖ ≤ J := fun x ↦ hJ _ (mem_range_self x)
  exact ⟨J, (norm_nonneg _).trans (hJ' 0), hJ'⟩

end OAI.Analysis.PDE.Weak
