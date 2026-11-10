module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.Regularity
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded
public import OAI.Analysis.PDE.Weak.Elliptic.TestSupport
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
public import OAI.Analysis.PDE.Variational.LocalizedEquation
public import OAI.Analysis.PDE.Weak.Elliptic.H1Neighborhood
public import OAI.Analysis.PDE.Weak.Elliptic.RegularSource


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Every finite level of interior weak regularity follows from the actual
divergence equation, by iterating the difference-quotient energy estimate. -/
theorem interior_regular_near_point
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : SmoothBounded A) {lam : ℝ} (hlam : 0 < lam) (k : ℕ)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (hell : ∀ x ∈ Ω, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))) (hf : WeakRegularity Ω k f)
    (he : WeakDivergenceEquation Ω (fun y ↦ A y (p.2 y)) f)
    {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ Ω) :
    ∃ V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      H1Regularity V (k + 1) p := by
  induction k generalizing Ω p f with
  | zero =>
    obtain ⟨V, hV, hxV, hsub, hd⟩ := interior_H1_derivatives_near_point
      A (hA.1.of_le (by simp)) hlam hΩ hell p hp f he hx
    refine ⟨V, hV, hxV, hsub, ?_⟩
    intro i
    obtain ⟨q, hq, hdv, hdg⟩ := hd i
    exact ⟨q, hq, hdv, hdg, trivial⟩
  | succ k ih =>
    obtain ⟨U, hU, hxU, hUΩ, hreg⟩ := ih hΩ hell p hp f hf.pred he hx
    have hgradreg := OAI.Analysis.PDE.Weak.H1Regularity.gradient hreg
    choose Q hQ hQv hQg hQr using hreg
    have heU : WeakDivergenceEquation U (fun y ↦ A y (p.2 y)) f :=
      OAI.Analysis.PDE.Variational.weakEquation_congr_on he hUΩ (Eventually.of_forall fun _ _ ↦ rfl)
        (Eventually.of_forall fun _ _ ↦ rfl)
    have hnext (j : Fin (m + 1)) :
        ∃ W : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
          H1Regularity W (k + 1) (Q j) := by
      obtain ⟨fd, hfd, hfdreg⟩ := hf j
      obtain ⟨F, hF, heF⟩ := differentiated_equation_regular A hA p.2
        (fun i ↦ (Q i).2) hQg hgradreg.pred (fun i ↦ (hQr i).gradient)
        f fd (hfdreg.mono_domain hUΩ) j (hfd.mono volume hUΩ) heU
      exact ih hU (fun y hy z ↦ hell y (hUΩ hy) z) (Q j) (hQ j) F hF heF hxU
    choose W hW hxW hWU hWr using hnext
    let V := U ∩ ⋂ j, W j
    have hVU : V ⊆ U := inter_subset_left
    have hVW (j : Fin (m + 1)) : V ⊆ W j := fun y hy ↦ mem_iInter.mp hy.2 j
    refine ⟨V, hU.inter (isOpen_iInter_of_finite hW), ⟨hxU, mem_iInter.mpr hxW⟩,
      hVU.trans hUΩ, ?_⟩
    intro j
    exact ⟨Q j, hQ j, (hQv j).mono volume hVU, (hQg j).mono volume hVU,
      (hWr j).mono_domain (hVW j)⟩

end OAI.Analysis.PDE.Weak
