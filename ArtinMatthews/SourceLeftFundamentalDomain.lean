module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
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
public import OAI.NumberTheory.ArithmeticGroups.Lattices.FiniteDomainMeasureRigidity


set_option backward.privateInPublic true
@[expose] public section

/-! Opposite-group transport of measurable fundamental domains to left cosets. -/
namespace ArtinMatthews
open MeasureTheory Set Topology
open scoped Classical
noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private def sourceLeftOpMeasurableEquiv : G ≃ᵐ Gᵐᵒᵖ where
  toEquiv := MulOpposite.opEquiv
  measurable_toFun := measurable_mul_op
  measurable_invFun := measurable_mul_unop

private def sourceLeftSubgroupOpHomeomorph (Γ : Subgroup G) : Γ ≃ₜ Γ.op where
  toEquiv := Γ.equivOp
  continuous_toFun := by
    change Continuous (fun x : Γ => (⟨MulOpposite.op x.val, x.property⟩ : Γ.op))
    exact (MulOpposite.continuous_op.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    change Continuous (fun x : Γ.op => (⟨x.val.unop, x.property⟩ : Γ))
    exact (MulOpposite.continuous_unop.comp continuous_subtype_val).subtype_mk _

theorem sourceLeftFundamentalDomain_exists_subset (Γ : Subgroup G)
    [DiscreteTopology Γ] [Countable Γ] (μ : Measure G) (D : Set G)
    (hD : MeasurableSet D) (hcover : ∀ x : G, ∃ γ : Γ, γ • x ∈ D) :
    ∃ F ⊆ D, MeasurableSet F ∧ IsFundamentalDomain Γ F μ := by
  have : SecondCountableTopology Gᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : G ≃ₜ Gᵐᵒᵖ).symm.isEmbedding.secondCountableTopology
  have : BorelSpace Gᵐᵒᵖ :=
    (sourceLeftOpMeasurableEquiv (G := G)).symm.measurableEmbedding.borelSpace
      (MulOpposite.opHomeomorph : G ≃ₜ Gᵐᵒᵖ).symm.isInducing
  have : DiscreteTopology Γ.op :=
    (sourceLeftSubgroupOpHomeomorph Γ).symm.isEmbedding.discreteTopology
  have : Countable Γ.op := (Γ.equivOp).symm.injective.countable
  let e : (Γ.op).op ≃ Γ := (Γ.equivOp.trans (Γ.op.equivOp)).symm
  let ν : Measure Gᵐᵒᵖ := μ.map MulOpposite.op
  have hDop : MeasurableSet (MulOpposite.op '' D) :=
    (sourceLeftOpMeasurableEquiv (G := G)).measurableEmbedding.measurableSet_image.mpr hD
  have hcoverop : ∀ x : Gᵐᵒᵖ, ∃ γ : (Γ.op).op, γ • x ∈ MulOpposite.op '' D := by
    intro x
    obtain ⟨γ, hγ⟩ := hcover x.unop
    refine ⟨e.symm γ, γ • x.unop, hγ, ?_⟩
    rfl
  obtain ⟨F, hFsub, hFm, hF⟩ :=
    OAI.NumberTheory.ArithmeticGroups.Lattices.FiniteDomainMeasureRigidity.Construction.exists_fundamentalDomain_subset_of_discrete
      Γ.op ν (MulOpposite.op '' D) hDop hcoverop
  refine ⟨MulOpposite.op ⁻¹' F, ?_, hFm.preimage measurable_mul_op, ?_⟩
  · intro x hx
    obtain ⟨y, hy, he⟩ := hFsub hx
    exact MulOpposite.op_injective he ▸ hy
  · have hmp : MeasurePreserving (MulOpposite.op : G → Gᵐᵒᵖ) μ ν :=
      ⟨measurable_mul_op, rfl⟩
    exact hF.preimage_of_equiv hmp.quasiMeasurePreserving e.bijective (fun γ x => rfl)

theorem sourceLeftFundamentalDomain_exists (Γ : Subgroup G)
    [DiscreteTopology Γ] [Countable Γ] (μ : Measure G) :
    ∃ F : Set G, MeasurableSet F ∧ IsFundamentalDomain Γ F μ := by
  obtain ⟨F, _, hFm, hF⟩ := sourceLeftFundamentalDomain_exists_subset Γ μ Set.univ
    MeasurableSet.univ (fun x => ⟨1, Set.mem_univ _⟩)
  exact ⟨F, hFm, hF⟩

end
end ArtinMatthews
