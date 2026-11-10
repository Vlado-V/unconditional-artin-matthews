module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.L2
public import OAI.Analysis.PDE.Variational.CellL2
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
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
public import OAI.Analysis.PDE.Green.GreenReal
public import OAI.Analysis.PDE.Weak.Elliptic.TestSupport


set_option backward.privateInPublic true
@[expose] public section

/-! The graph closure of genuine compactly supported smooth gradients. -/

noncomputable section
open Set _root_.MeasureTheory
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

abbrev H1Pair (m : ℕ) :=
  Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) ×
    Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))

def smoothH1Pair (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hu : ContDiff ℝ ∞ u)
    (hs : HasCompactSupport u) : H1Pair m :=
  ⟨(hu.continuous.memLp_of_hasCompactSupport hs).toLp u,
    ((OAI.Analysis.PDE.Variational.continuous_cellGradient (hu.of_le (by simp))).memLp_of_hasCompactSupport
      (hasCompactSupport_cellGradient hs)).toLp (OAI.Analysis.PDE.Variational.cellGradient u)⟩

def smoothH1Graph (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) : Set (H1Pair m) :=
  {p | ∃ (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hu : ContDiff ℝ ∞ u) (hs : HasCompactSupport u),
    tsupport u ⊆ Ω ∧ smoothH1Pair u hu hs = p}

def H1Zero (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) : Set (H1Pair m) := closure (smoothH1Graph Ω)

theorem smoothH1Pair_value_ae (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hu : ContDiff ℝ ∞ u)
    (hs : HasCompactSupport u) : (smoothH1Pair u hu hs).1 =ᵐ[volume] u :=
  (hu.continuous.memLp_of_hasCompactSupport hs).coeFn_toLp

theorem smoothH1Pair_gradient_ae (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hu : ContDiff ℝ ∞ u)
    (hs : HasCompactSupport u) : (smoothH1Pair u hu hs).2 =ᵐ[volume] OAI.Analysis.PDE.Variational.cellGradient u :=
  ((OAI.Analysis.PDE.Variational.continuous_cellGradient (hu.of_le (by simp))).memLp_of_hasCompactSupport
      (hasCompactSupport_cellGradient hs)).coeFn_toLp

theorem smoothH1Pair_mem_H1Zero {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hu : ContDiff ℝ ∞ u) (hs : HasCompactSupport u)
    (hΩ : tsupport u ⊆ Ω) : smoothH1Pair u hu hs ∈ H1Zero Ω :=
  subset_closure ⟨u, hu, hs, hΩ, rfl⟩

theorem smoothH1Pair_difference_bound (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hu : ContDiff ℝ ∞ u) (hs : HasCompactSupport u) (j : Fin (m + 1))
    {h : ℝ} (hh : h ≠ 0) :
    ‖differenceQuotientL2 volume (Pi.single j 1) h (smoothH1Pair u hu hs).1‖ ≤
      ‖(smoothH1Pair u hu hs).2‖ := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by simp)
  let du := fun x ↦ fderiv ℝ u x (Pi.single j 1)
  have hdc : Continuous du := OAI.Analysis.PDE.Green.continuous_directional hu1 (Pi.single j 1)
  have hds : HasCompactSupport du := hs.fderiv_apply (𝕜 := ℝ) _
  have hd : MemLp du 2 volume := hdc.memLp_of_hasCompactSupport hds
  have hg : MemLp (OAI.Analysis.PDE.Variational.cellGradient u) 2 volume :=
    (OAI.Analysis.PDE.Variational.continuous_cellGradient hu1).memLp_of_hasCompactSupport (hasCompactSupport_cellGradient hs)
  refine (norm_differenceQuotientL2_smooth_le volume hu1
    (hu.continuous.memLp_of_hasCompactSupport hs) (Pi.single j 1) hh hd).trans ?_
  change ‖hd.toLp du‖ ≤ ‖hg.toLp (OAI.Analysis.PDE.Variational.cellGradient u)‖
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [OAI.Analysis.PDE.Variational.norm_sq_toLp_eq_integral, OAI.Analysis.PDE.Variational.norm_sq_toLp_eq_integral]
  apply integral_mono
    ((memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd)
    ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)
  intro x
  exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (OAI.Analysis.PDE.Variational.cellGradient u x) j) 2

/-- Uniform difference-quotient control survives the actual strong graph
completion. This is not an assumed weak differentiability estimate. -/
theorem H1Zero.difference_bound {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {p : H1Pair m}
    (hp : p ∈ H1Zero Ω) (j : Fin (m + 1)) {h : ℝ} (hh : h ≠ 0) :
    ‖differenceQuotientL2 volume (Pi.single j 1) h p.1‖ ≤ ‖p.2‖ := by
  have hc : IsClosed {q : H1Pair m |
      ‖differenceQuotientL2 volume (Pi.single j 1) h q.1‖ ≤ ‖q.2‖} :=
    isClosed_le (((differenceQuotientL2 volume (Pi.single j 1) h).continuous.comp
      continuous_fst).norm) continuous_snd.norm
  apply closure_minimal (s := smoothH1Graph Ω) _ hc hp
  rintro q ⟨u, hu, hs, _, rfl⟩
  exact smoothH1Pair_difference_bound u hu hs j hh

end OAI.Analysis.PDE.Weak
