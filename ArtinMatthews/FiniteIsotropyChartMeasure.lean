module

public import ArtinMatthews.FiniteIsotropyChart
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import ArtinMatthews.FiniteIsotropyProjectionMeasure
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


set_option backward.privateInPublic true
@[expose] public section

/-! The exact reciprocal-stabilizer measure on a selected orbifold chart. -/
namespace ArtinMatthews
open Set MeasureTheory Topology
open scoped ENNReal Pointwise Classical
noncomputable section

variable {Γ X : Type*} [Group Γ] [TopologicalSpace X] [MulAction Γ X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {p : X}

def sourceFiniteChartDomainMeasure (c : SourceFiniteIsotropyChart Γ X p) (ξ : Measure X) :
    Measure c.domain := ξ.comap Subtype.val

theorem sourceFiniteChartProjection_map (c : SourceFiniteIsotropyChart Γ X p) (ξ : Measure X) :
    (sourceFiniteChartDomainMeasure c ξ).map (sourceFiniteChartProjection c) =
      (ξ.restrict (c.domain : Set X)).map (Quotient.mk (MulAction.orbitRel Γ X)) := by
  change (ξ.comap (Subtype.val : c.domain → X)).map
    (Quotient.mk (MulAction.orbitRel Γ X) ∘ Subtype.val) = _
  have hq : Measurable (Quotient.mk (MulAction.orbitRel Γ X)) :=
    measurable_quotient_mk' (s := MulAction.orbitRel Γ X)
  calc
    _ = ((ξ.comap (Subtype.val : c.domain → X)).map Subtype.val).map
        (Quotient.mk (MulAction.orbitRel Γ X)) :=
      (Measure.map_map hq measurable_subtype_coe).symm
    _ = _ := by
      apply congrArg (Measure.map (Quotient.mk (MulAction.orbitRel Γ X)))
      exact map_comap_subtype_coe (s := (c.domain : Set X)) c.isOpen_domain.measurableSet ξ

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem sourceFiniteChart_weight_pos (c : SourceFiniteIsotropyChart Γ X p) :
    0 < (Nat.card (MulAction.stabilizer Γ p) : ℝ≥0∞)⁻¹ ∧
      (Nat.card (MulAction.stabilizer Γ p) : ℝ≥0∞)⁻¹ ≠ ⊤ := by
  let : Fintype (MulAction.stabilizer Γ p) := c.finite_stabilizer.fintype
  have hn : (Nat.card (MulAction.stabilizer Γ p) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.card_pos.ne' : Nat.card (MulAction.stabilizer Γ p) ≠ 0)
  exact ⟨ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _), ENNReal.inv_ne_top.mpr hn⟩

variable [Countable Γ] [ContinuousConstSMul Γ X]
    {G : Type*} [MulAction Γ G] [MeasurableSpace G] [MeasurableConstSMul Γ G]
    (μ : Measure G) [SMulInvariantMeasure Γ G μ]
    (ν : Measure (Quotient (MulAction.orbitRel Γ G)))
    [QuotientMeasureEqMeasurePreimage (G := Γ) μ ν]
    (ξ : Measure X) (π : G → X) (hπ : MeasurePreserving π μ ξ)
    (hπγ : ∀ (γ : Γ) (g : G), π (γ • g) = γ • π g)
    (r : Quotient (MulAction.orbitRel Γ G) → Quotient (MulAction.orbitRel Γ X))
    (hr : Measurable r)
    (hrπ : ∀ g : G, r (Quotient.mk (MulAction.orbitRel Γ G) g) =
      Quotient.mk (MulAction.orbitRel Γ X) (π g))

include hπ hπγ hr hrπ

theorem sourceFiniteChartProjection_measurePreserving
    {F : Set G} (hF : IsFundamentalDomain Γ F μ) (c : SourceFiniteIsotropyChart Γ X p) :
    MeasurePreserving (sourceFiniteChartProjection c)
      ((Nat.card (MulAction.stabilizer Γ p) : ℝ≥0∞)⁻¹ • sourceFiniteChartDomainMeasure c ξ)
      ((ν.map r).restrict (Set.range (sourceFiniteChartProjection c))) := by
  let : Fintype (MulAction.stabilizer Γ p) := c.finite_stabilizer.fintype
  have hRange : Quotient.mk (MulAction.orbitRel Γ X) '' (c.domain : Set X) =
      Set.range (sourceFiniteChartProjection c) := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
  have hImage : MeasurableSet (Quotient.mk (MulAction.orbitRel Γ X) '' (c.domain : Set X)) := by
    rw [hRange]
    apply measurableSet_quotient.mpr
    exact ((sourceFiniteChartProjection_range_open c).preimage continuous_quot_mk).measurableSet
  have hstable : ∀ h : MulAction.stabilizer Γ p, ∀ x ∈ c.domain, (h : Γ) • x ∈ c.domain := by
    intro h x hx
    exact c.domain.smul_mem h hx
  have hsep : ∀ γ : Γ, ∀ x ∈ c.domain, γ • x ∈ c.domain →
      γ ∈ MulAction.stabilizer Γ p := by
    intro γ x hx hγx
    by_contra hγ
    exact Set.disjoint_left.mp (c.separated γ hγ) ⟨x, hx, rfl⟩ hγx
  have hmeas : Measurable (sourceFiniteChartProjection c) :=
    (measurable_quotient_mk' (s := MulAction.orbitRel Γ X)).comp measurable_subtype_coe
  refine ⟨hmeas, ?_⟩
  rw [Measure.map_smul _ hmeas.aemeasurable, sourceFiniteChartProjection_map]
  symm
  rw [← hRange]
  exact sourceFiniteSlice_projection_measure μ ν ξ π hπ hπγ r hr hrπ
    (MulAction.stabilizer Γ p) hF (c.domain : Set X) c.isOpen_domain.measurableSet
    hImage hstable hsep

end
end ArtinMatthews
