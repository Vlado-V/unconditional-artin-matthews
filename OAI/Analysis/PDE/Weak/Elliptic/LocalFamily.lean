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
public import OAI.Analysis.PDE.Weak.Elliptic.CutoffExistence
public import OAI.Analysis.PDE.Weak.Elliptic.DerivativeFamily
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothInterior


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- A local weak derivative hierarchy has a compactly supported global
representative hierarchy agreeing with the original field near the point. -/
theorem weakRegularity_local_family
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω) {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ Ω)
    {k : ℕ} {u : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : WeakRegularity Ω k u) :
    ∃ (V K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m))
      (U : List (Fin (m + 1)) → Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ IsCompact K ∧ K ⊆ Ω ∧
      (∀ᵐ y ∂volume, y ∈ V → U [] y = u y) ∧
      (∀ α, α.length ≤ k → ∀ᵐ y ∂volume, y ∉ K → U α y = 0) ∧
      (∀ α, α.length < k → ∀ i,
        HasWeakDirectionalDerivative volume (Pi.single i 1) (U α) (U (i :: α))) := by
  obtain ⟨η, V, hV, hxV, hVΩ, hη, hηs, hηsub, hηrange, hηone⟩ :=
    exists_cutoff_with_open_plateau hΩ hx
  let A : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ →L[ℝ] ℝ := fun y ↦ η y • ContinuousLinearMap.id ℝ ℝ
  have hA : ContDiff ℝ ∞ A := hη.smul contDiff_const
  have hAs : HasCompactSupport A := hηs.smul_right
  have hAsub : tsupport A ⊆ tsupport η := tsupport_smul_subset_left η _
  obtain ⟨M, hM⟩ := (smoothBounded_of_hasCompactSupport hA hAs).bound
  let v := fieldMultiplierCLM (μ := volume) A hA.continuous.aestronglyMeasurable
    (Eventually.of_forall hM) u
  have hv : SupportedRegularity (tsupport η) k v :=
    hu.compact_operator_mul A hA hAs hAsub (hAsub.trans hηsub) hM
  obtain ⟨U, hU, hUs, hUd⟩ := supportedRegularity_derivative_family hv
  refine ⟨V, tsupport η, U, hV, hxV, hVΩ, hηs, hηsub, ?_, hUs, hUd⟩
  rw [hU]
  filter_upwards [fieldMultiplierCLM_ae A hA.continuous.aestronglyMeasurable
    (Eventually.of_forall hM) u] with y hy
  intro hyV
  rw [hy]
  change η y * u y = u y
  rw [hηone y hyV, one_mul]

/-- The actual weak elliptic equation with smooth local data supplies the
complete compactly supported derivative family used in Sobolev embedding. -/
theorem smooth_elliptic_local_derivative_family
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
    ∃ (V K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m))
      (U : List (Fin (m + 1)) → Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ IsCompact K ∧ K ⊆ Ω ∧
      (∀ᵐ y ∂volume, y ∈ V → U [] y = p.1 y) ∧
      (∀ α, α.length ≤ k → ∀ᵐ y ∂volume, y ∉ K → U α y = 0) ∧
      (∀ α, α.length < k → ∀ i,
        HasWeakDirectionalDerivative volume (Pi.single i 1) (U α) (U (i :: α))) := by
  obtain ⟨W, hW, hxW, hWΩ, hreg⟩ := smooth_interior_regular_near_point
    A hA hlam k hΩ hell p hp f g hg hfg he hx
  obtain ⟨V, K, U, hV, hxV, hVW, hK, hKW, hU, hUs, hUd⟩ :=
    weakRegularity_local_family hW hxW hreg.value.pred
  exact ⟨V, K, U, hV, hxV, hVW.trans hWΩ, hK, hKW.trans hWΩ, hU, hUs, hUd⟩

end OAI.Analysis.PDE.Weak
