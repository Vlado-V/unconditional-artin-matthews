module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.Regularity
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
public import OAI.Analysis.PDE.Weak.Elliptic.CutoffExistence
public import OAI.Analysis.PDE.Weak.Elliptic.InteriorRegularity
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothExtension
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothRegularity


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Smooth local coefficients and smooth local data give every finite order
of actual weak interior regularity. No global coefficient bounds are assumed. -/
theorem smooth_interior_regular_near_point
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {lam : ℝ} (hlam : 0 < lam) (k : ℕ)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (hell : ∀ x ∈ Ω, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐ x ∂volume, x ∈ Ω → f x = g x)
    (he : WeakDivergenceEquation Ω (fun y ↦ A y (p.2 y)) f)
    {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ Ω) :
    ∃ V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      H1Regularity V (k + 1) p := by
  obtain ⟨θ, U, hU, hxU, hUΩ, hθ, hθs, hθsub, hθrange, hθone⟩ :=
    exists_cutoff_with_open_plateau hΩ hx
  let B := ellipticExtension A θ lam
  have hB : SmoothBounded B := ellipticExtension_smoothBounded hA hθ hθs lam
  have hBe : ∀ y z, lam * ‖z‖ ^ 2 ≤ inner ℝ (B y z) z :=
    ellipticExtension_elliptic hθrange hθsub hell
  let gθ := fun y ↦ θ y * g y
  have hgθ : ContDiff ℝ ∞ gθ := hθ.mul hg
  have hsθ : HasCompactSupport gθ := hθs.mul_right
  let fθ : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) :=
    (hgθ.continuous.memLp_of_hasCompactSupport hsθ).toLp gθ
  have hfθ : WeakRegularity U k fθ := weakRegularity_of_smooth_compact hgθ hsθ U k
  have heB : WeakDivergenceEquation U (fun y ↦ B y (p.2 y)) fθ := by
    apply OAI.Analysis.PDE.Variational.weakEquation_congr_on he hUΩ
    · apply Eventually.of_forall
      intro y hy
      rw [show B y = A y from ellipticExtension_eq lam (hθone y hy)]
    · filter_upwards [hfg, (hgθ.continuous.memLp_of_hasCompactSupport hsθ).coeFn_toLp] with y hy hz
      intro hyU
      rw [hz, hy (hUΩ hyU)]
      change θ y * g y = g y
      rw [hθone y hyU, one_mul]
  obtain ⟨V, hV, hxV, hVU, hreg⟩ := interior_regular_near_point B hB hlam k hU
    (fun y _ z ↦ hBe y z) p hp fθ hfθ heB hxU
  exact ⟨V, hV, hxV, hVU.trans hUΩ, hreg⟩

end OAI.Analysis.PDE.Weak
