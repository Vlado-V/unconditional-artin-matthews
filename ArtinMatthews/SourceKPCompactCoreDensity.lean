module

public import ArtinMatthews.SourceKPCompactCoreMass
public import ArtinMatthews.SourceKPAutomorphicCompactTopology
public import ArtinMatthews.SourceKPCompactChartMassTest
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The true compact scalar test core is dense in the canonical automorphic Haar L2 space. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen Filter TopologicalSpace
open scoped NumberField MatrixGroups AdeleRing Topology ENNReal Classical InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "T" => sourceKPCompactC2Core K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "ν" => productVolume (InfinitePlace K)

theorem sourceKPCompactCoreMass_separates_chart (g : Lp ℂ 2 μ)
    (hg : ∀ φ : T, inner ℂ (sourceKPCompactCoreMass K hζ 2 φ) g = 0)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    ∀ᵐ y ∂(μ).restrict (Set.range (sourceKPFiniteChartProjection K hζ b p)), g y = 0 := by
  let U := sourceKPFiniteChartCoordinateDomain K hζ b p
  let R := Set.range (sourceKPFiniteChartProjection K hζ b p)
  let H := SourceKPFiniteChartStabilizer K hζ b p
  let G := sourceKPCompactChartMassLift K hζ b p g
  let q := sourceKPCompactCoordinateProjection K hζ b
  have hU := sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p
  have hd := h1LocalTestMass_denseRange U hU (sourceKPFiniteChartCoordinateDomain_upper K hζ b p)
  have hG : inner ℂ G.val G.val = 0 :=
    hd.induction_on (p := fun v : h1SupportedMass U => inner ℂ v.val G.val = 0) G
      (isClosed_eq (continuous_subtype_val.inner continuous_const) continuous_const)
      (fun φ => (sourceKPCompactChartMassLift_inner K hζ b p φ g).trans
        (hg (sourceKPChartPeriodizationCore K hζ b φ.val)))
  have hz : G.val = 0 := inner_self_eq_zero.mp hG
  have hzfun : ∀ᵐ x ∂ν, (0 : H1Mass (InfinitePlace K)) x = 0 := Lp.coeFn_zero ℂ 2 ν
  have h0 : ∀ᵐ x ∂(ν).restrict U, g (q x) = 0 := by
    filter_upwards [ae_restrict_of_ae (sourceKPCompactChartMassLift_coe K hζ b p g),
      ae_restrict_of_ae hzfun,
      ae_restrict_mem hU.measurableSet] with x hx hz0 hxu
    change G.val x = (U).indicator (g ∘ q) x at hx
    rw [hz,hz0,Set.indicator_of_mem hxu] at hx
    exact hx.symm
  let hm := sourceKPCompactCoordinateProjection_measurePreserving K hζ b p
  have h := Measure.ae_smul_measure h0 ((Nat.card H : ℝ≥0∞)⁻¹)
  have hm0 : MeasurableSet { y | g y = 0 } :=
    measurableSet_eq_fun (Lp.stronglyMeasurable g).measurable measurable_const
  change ∀ᵐ y ∂(μ).restrict R, g y = 0
  rw [← hm.map_eq]
  exact (ae_map_iff hm.measurable.aemeasurable hm0).mpr h

theorem sourceKPCompactCoreMass_separates (g : Lp ℂ 2 μ)
    (hg : ∀ φ : T, inner ℂ (sourceKPCompactCoreMass K hζ 2 φ) g = 0) : g = 0 := by
  choose b p hp using sourceKPUpperToCompact_cover K hζ
  let V : Y → Set Y := fun y => Set.range (sourceKPFiniteChartProjection K hζ (b y) (p y))
  have ho (y : Y) : IsOpen (V y) := sourceKPFiniteChart_range_open K hζ (b y) (p y)
  have hv (y : Y) : y ∈ V y :=
    ⟨⟨p y,(sourceKPUpperFiniteChart K hζ (b y) (p y)).center_mem⟩,hp y⟩
  obtain ⟨S,hS,hcover⟩ := TopologicalSpace.countable_cover_nhds (fun y => (ho y).mem_nhds (hv y))
  letI : Countable S := hS.to_subtype
  have hlocal (s : S) : ∀ᵐ y ∂μ, y ∈ V s.val → g y = 0 :=
    (ae_restrict_iff' (ho s.val).measurableSet).mp
      (sourceKPCompactCoreMass_separates_chart K hζ g hg (b s.val) (p s.val))
  have hall : ∀ᵐ y ∂μ, ∀ s : S, y ∈ V s.val → g y = 0 := ae_all_iff.mpr hlocal
  apply Lp.ext
  have hzfun : ∀ᵐ y ∂μ, (0 : Lp ℂ 2 μ) y = 0 := Lp.coeFn_zero ℂ 2 μ
  filter_upwards [hall,hzfun] with y hy hz
  rw [hz]
  have hy' : y ∈ ⋃ x ∈ S, V x := by
    rw [hcover]
    exact Set.mem_univ y
  obtain ⟨x,hx,hxy⟩ := Set.mem_iUnion₂.mp hy'
  exact hy ⟨x,hx⟩ hxy

theorem sourceKPCompactCoreMass_denseRange :
    DenseRange (sourceKPCompactCoreMass K hζ 2) := by
  let A := (sourceKPCompactCoreMass K hζ 2).range
  have ha : Aᗮ = ⊥ := by
    apply (Aᗮ).eq_bot_iff.mpr
    intro g hg
    apply sourceKPCompactCoreMass_separates K hζ g
    intro f
    have hf : sourceKPCompactCoreMass K hζ 2 f ∈ A := ⟨f,rfl⟩
    exact Submodule.inner_right_of_mem_orthogonal hf hg
  have ht : A.topologicalClosure = ⊤ := by
    rw [← A.orthogonal_orthogonal_eq_closure,ha,Submodule.bot_orthogonal_eq_top]
  change Dense (A : Set (Lp ℂ 2 μ))
  rw [dense_iff_closure_eq,← Submodule.topologicalClosure_coe,ht,Submodule.top_coe]

end
end ArtinMatthews
