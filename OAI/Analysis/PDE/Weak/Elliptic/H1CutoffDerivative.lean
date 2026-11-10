module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.Cutoff
public import OAI.Analysis.PDE.Weak.Elliptic.Derivative
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
public import Mathlib.Order.CompletePartialOrder
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
public import OAI.Analysis.PDE.Weak.Elliptic.H1Derivative
public import OAI.Analysis.PDE.Weak.Elliptic.Localization
public import OAI.Analysis.PDE.Weak.Elliptic.VectorDifference


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- The localized energy bound controls the whole differentiated H¹
graph, including the terms in which a derivative hits the cutoff. -/
theorem exists_H1_derivative_cutoff_of_weighted_difference_bounds
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    {M K L J C : ℝ} (hM : ∀ x, |η x| ≤ M)
    (hK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K)
    (j : Fin (m + 1)) {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hs0 : ∀ n, s n ≠ 0)
    (hL : ∀ n x, |differenceQuotient (Pi.single j 1) (s n) η x| ≤ L)
    (hJ : ∀ n x, ‖differenceQuotient (Pi.single j 1) (s n) (OAI.Analysis.PDE.Variational.cellGradient η) x‖ ≤ J)
    (hC : ∀ n, ‖cutoffL2 η hη.continuous hM
      (differenceQuotientL2 volume (Pi.single j 1) (s n) p.2)‖ ≤ C) :
    ∃ q : H1Pair m, q ∈ H1Zero univ ∧
      HasWeakDirectionalDerivative volume (Pi.single j 1)
        (cutoffH1Pair η (hη.of_le (by simp)) hM hK p).1 q.1 ∧
      HasWeakDirectionalDerivative volume (Pi.single j 1)
        (cutoffH1Pair η (hη.of_le (by simp)) hM hK p).2 q.2 := by
  let pη := cutoffH1Pair η (hη.of_le (by simp)) hM hK p
  have hpη : pη ∈ H1Zero univ :=
    OAI.Analysis.PDE.Weak.H1Zero.cutoff hp η hη hM hK (subset_univ _)
  have hv0 : Integrable (pη.1 : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) :=
    integrable_cutoffL2 volume η hη.continuous hηs hM p.1
  have hv1 : Integrable (pη.2 : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m) := by
    have ha := integrable_cutoffL2 volume η hη.continuous hηs hM p.2
    have hb := integrable_vectorProductL2 volume (OAI.Analysis.PDE.Variational.cellGradient η)
      (OAI.Analysis.PDE.Variational.continuous_cellGradient (hη.of_le (by simp)))
      (hasCompactSupport_cellGradient hηs) hK p.1
    exact (ha.add hb).congr (Lp.coeFn_add _ _).symm
  apply exists_H1_derivative_of_difference_bounds pη hv0 hv1 (Pi.single j 1) hs hs0
    (fun n ↦ OAI.Analysis.PDE.Weak.H1Zero.difference hpη _ _ (subset_refl _) (subset_univ _))
    (fun n ↦ OAI.Analysis.PDE.Weak.H1Zero.difference_bound hpη j (hs0 n))
  intro n
  change ‖differenceQuotientL2 volume (Pi.single j 1) (s n)
    (cutoffL2 η hη.continuous hM p.2 +
      vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient (hη.of_le (by simp))) hK p.1)‖ ≤
    (C + L * ‖p.2‖) + (K * ‖p.2‖ + J * ‖p.1‖)
  rw [map_add]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_differenceQuotientL2_cutoff_le volume η hη.continuous hM
      (Pi.single j 1) (s n) (hL n) p.2).trans (add_le_add (hC n) le_rfl)
  · apply (norm_differenceQuotientL2_vectorProduct_le volume (OAI.Analysis.PDE.Variational.cellGradient η)
      (OAI.Analysis.PDE.Variational.continuous_cellGradient (hη.of_le (by simp))) hK
      (Pi.single j 1) (s n) (hJ n) p.1).trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left (OAI.Analysis.PDE.Weak.H1Zero.difference_bound hp j (hs0 n))
        ((norm_nonneg _).trans (hK 0))) le_rfl

end OAI.Analysis.PDE.Weak
