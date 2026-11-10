module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Variational.CellL2
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

noncomputable section
open Set _root_.MeasureTheory Filter
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem continuous_eqOn_of_local_ae
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω) {u v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω)
    (heq : ∀ᵐ x ∂volume, x ∈ Ω → u x = v x) : EqOn u v Ω := by
  have hae : u =ᵐ[volume.restrict Ω] v := by
    change ∀ᵐ x ∂volume.restrict Ω, u x = v x
    exact (ae_restrict_iff' hΩ.measurableSet).mpr heq
  exact Measure.eqOn_open_of_ae_eq (μ := volume) hae hΩ hu hv

theorem contDiffOn_of_local_ae_representatives
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (_ : IsOpen Ω) {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hu : ContinuousOn u Ω) (q : ℕ)
    (hlocal : ∀ x ∈ Ω, ∃ (V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ ContDiff ℝ q v ∧
        (∀ᵐ y ∂volume, y ∈ V → u y = v y)) : ContDiffOn ℝ q u Ω := by
  intro x hx
  obtain ⟨V, v, hV, hxV, hVΩ, hv, hae⟩ := hlocal x hx
  have heq := continuous_eqOn_of_local_ae hV (hu.mono hVΩ) hv.continuous.continuousOn hae
  have hevent : u =ᶠ[𝓝 x] v := Filter.eventuallyEq_of_mem (hV.mem_nhds hxV) heq
  exact (hv.contDiffAt.congr_of_eventuallyEq hevent).contDiffWithinAt

/-- Finite-order local representatives of one continuous function give a
single smooth representative; equality is pointwise on each open overlap. -/
theorem smoothOn_of_local_finite_representatives
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω) {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hu : ContinuousOn u Ω)
    (hlocal : ∀ q : ℕ, ∀ x ∈ Ω,
      ∃ (V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ),
        IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ ContDiff ℝ q v ∧
          (∀ᵐ y ∂volume, y ∈ V → u y = v y)) : ContDiffOn ℝ ∞ u Ω := by
  apply contDiffOn_infty.mpr
  intro q
  exact contDiffOn_of_local_ae_representatives hΩ hu q (hlocal q)

/-- Compatible local continuous representatives glue to one representative.
A countable open subcover is used only to combine the almost-everywhere
identities; compatibility on overlaps is pointwise. -/
theorem exists_contDiffOn_representative
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (_ : IsOpen Ω) (f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (q : ℕ)
    (hlocal : ∀ x ∈ Ω, ∃ (V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ ContDiff ℝ q v ∧
        (∀ᵐ y ∂volume, y ∈ V → f y = v y)) :
    ∃ u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiffOn ℝ q u Ω ∧
      (∀ᵐ y ∂volume, y ∈ Ω → u y = f y) := by
  classical
  choose V v hV hxV hVΩ hv hfv using fun a : Ω ↦ hlocal a a.property
  have hcompat (a b : Ω) : EqOn (v a) (v b) (V a ∩ V b) := by
    apply continuous_eqOn_of_local_ae ((hV a).inter (hV b))
      (hv a).continuous.continuousOn (hv b).continuous.continuousOn
    filter_upwards [hfv a, hfv b] with y ha hb
    intro hy
    exact (ha hy.1).symm.trans (hb hy.2)
  let u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ := fun y ↦ if h : y ∈ Ω then v ⟨y, h⟩ y else 0
  have huV (a : Ω) : EqOn u (v a) (V a) := by
    intro y hy
    have hyΩ := hVΩ a hy
    change (if h : y ∈ Ω then v ⟨y, h⟩ y else 0) = v a y
    rw [dite_eq_left hyΩ]
    exact hcompat ⟨y, hyΩ⟩ a ⟨hxV ⟨y, hyΩ⟩, hy⟩
  have hu : ContDiffOn ℝ q u Ω := by
    intro x hx
    let a : Ω := ⟨x, hx⟩
    have hevent : u =ᶠ[𝓝 x] v a :=
      Filter.eventuallyEq_of_mem ((hV a).mem_nhds (hxV a)) (huV a)
    exact ((hv a).contDiffAt.congr_of_eventuallyEq hevent).contDiffWithinAt
  have hcover : Ω ⊆ ⋃ a : Ω, V a := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨t, ht, htcov⟩ := (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover V hV hcover
  let : Countable t := ht.to_subtype
  have ha (a : t) : ∀ᵐ y ∂volume, y ∈ V a.val → u y = f y := by
    filter_upwards [hfv a.val] with y hy
    intro hyV
    exact (huV a.val hyV).trans (hy hyV).symm
  refine ⟨u, hu, ?_⟩
  filter_upwards [ae_all_iff.mpr ha] with y hy
  intro hyΩ
  obtain ⟨a, ha⟩ := mem_iUnion.mp (htcov hyΩ)
  obtain ⟨hat, hay⟩ := mem_iUnion.mp ha
  exact hy ⟨a, hat⟩ hay

theorem exists_smoothOn_representative
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω) (f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hlocal : ∀ q : ℕ, ∀ x ∈ Ω,
      ∃ (V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ),
        IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ ContDiff ℝ q v ∧
          (∀ᵐ y ∂volume, y ∈ V → f y = v y)) :
    ∃ u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiffOn ℝ ∞ u Ω ∧
      (∀ᵐ y ∂volume, y ∈ Ω → u y = f y) := by
  obtain ⟨u, hu, hue⟩ := exists_contDiffOn_representative hΩ f 2 (hlocal 2)
  refine ⟨u, smoothOn_of_local_finite_representatives hΩ hu.continuousOn ?_, hue⟩
  intro q x hx
  obtain ⟨V, v, hV, hxV, hVΩ, hv, hfv⟩ := hlocal q x hx
  refine ⟨V, v, hV, hxV, hVΩ, hv, ?_⟩
  filter_upwards [hue, hfv] with y hy hz
  intro hyV
  exact (hy (hVΩ hyV)).trans (hz hyV)

end OAI.Analysis.PDE.Weak
