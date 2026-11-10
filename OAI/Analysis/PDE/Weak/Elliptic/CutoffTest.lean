module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Boundary.H1Translation
public import OAI.Analysis.PDE.Weak.Elliptic.Cutoff
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.PDE.Weak.Elliptic.Coefficient


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure X}

omit [NormedSpace ℝ X] in
theorem vectorProductL2_cutoff (η : X → ℝ) (hη : Continuous η) {M : ℝ}
    (hM : ∀ x, |η x| ≤ M) (g : X → E) (hg : Continuous g) {K : ℝ}
    (hK : ∀ x, ‖g x‖ ≤ K) (u : Lp ℝ 2 μ) :
    vectorProductL2 g hg hK (cutoffL2 η hη hM u) =
      cutoffL2 η hη hM (vectorProductL2 g hg hK u) := by
  apply Lp.ext
  filter_upwards [vectorProductL2_ae g hg hK (cutoffL2 η hη hM u),
    cutoffL2_ae η hη hM u, cutoffL2_ae η hη hM (vectorProductL2 g hg hK u),
    vectorProductL2_ae g hg hK u] with x hx hy hz hw
  rw [hx, hy, hz, hw]
  simp [smul_smul]

variable {m : ℕ}

theorem cutoffH1Pair_twice_gradient (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hη : ContDiff ℝ 1 η) {M K : ℝ}
    (hM : ∀ x, |η x| ≤ M) (hK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K) (p : H1Pair m) :
    (cutoffH1Pair η hη hM hK (cutoffH1Pair η hη hM hK p)).2 =
      cutoffL2 η hη.continuous hM
        (cutoffL2 η hη.continuous hM p.2 +
          (2 : ℝ) • vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK p.1) := by
  change cutoffL2 η hη.continuous hM
      (cutoffL2 η hη.continuous hM p.2 +
        vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK p.1) +
      vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK
        (cutoffL2 η hη.continuous hM p.1) = _
  rw [vectorProductL2_cutoff, map_add, map_add, map_smul]
  module

theorem cutoffH1Pair_twice_gradient_norm (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hη : ContDiff ℝ 1 η) {K : ℝ}
    (hM : ∀ x, |η x| ≤ 1) (hK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K) (p : H1Pair m) :
    ‖(cutoffH1Pair η hη hM hK (cutoffH1Pair η hη hM hK p)).2‖ ≤
      ‖cutoffL2 η hη.continuous hM p.2‖ +
        2 * ‖vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK p.1‖ := by
  rw [cutoffH1Pair_twice_gradient]
  calc
    _ ≤ 1 * ‖cutoffL2 η hη.continuous hM p.2 +
        (2 : ℝ) • vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK p.1‖ :=
      norm_cutoffL2_le η hη.continuous hM _
    _ ≤ _ := by
      simpa [norm_smul] using norm_add_le
        (cutoffL2 η hη.continuous hM p.2)
        ((2 : ℝ) • vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK p.1)

/-- The squared-cutoff difference test is admissible, and so is its
backward difference, whenever the actual cutoff and its translate fit. -/
theorem H1Zero.cutoff_difference_test {p : H1Pair m} (hp : p ∈ H1Zero univ)
    (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η) {M K : ℝ}
    (hM : ∀ x, |η x| ≤ M) (hK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K)
    (v : OAI.Analysis.PDE.Variational.CellCoordinates m) (h : ℝ) {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (hsub : tsupport η ⊆ Ω) (hshift : (fun x ↦ x + (-h) • v) ⁻¹' tsupport η ⊆ Ω) :
    let q := cutoffH1Pair η (hη.of_le (by simp)) hM hK
      (cutoffH1Pair η (hη.of_le (by simp)) hM hK (differenceH1Pair v h p))
    q ∈ H1Zero (tsupport η) ∧ differenceH1Pair v (-h) q ∈ H1Zero Ω := by
  dsimp only
  have hd := OAI.Analysis.PDE.Weak.H1Zero.difference hp v h (Subset.rfl) (subset_univ _)
  have hc := OAI.Analysis.PDE.Weak.H1Zero.cutoff hd η hη hM hK (inter_subset_left : tsupport η ∩ univ ⊆ tsupport η)
  have hcc := OAI.Analysis.PDE.Weak.H1Zero.cutoff hc η hη hM hK (inter_subset_left : tsupport η ∩ tsupport η ⊆ tsupport η)
  exact ⟨hcc, OAI.Analysis.PDE.Weak.H1Zero.difference hcc v (-h) hsub hshift⟩

end OAI.Analysis.PDE.Weak
