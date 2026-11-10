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


set_option backward.privateInPublic true
@[expose] public section

/-! Left multiplication identifies the quotients of conjugate subgroups. -/
namespace ArtinMatthews
open Set MeasureTheory
open scoped Pointwise Classical
noncomputable section

variable {G : Type*} [Group G]

abbrev sourceConjugateSubgroup (Γ : Subgroup G) (a : G) : Subgroup G :=
  Γ.map (MulAut.conj a).toMonoidHom

def sourceLeftQuotientConjugacy (Γ : Subgroup G) (a : G) :
    Quotient (QuotientGroup.rightRel Γ) ≃
      Quotient (QuotientGroup.rightRel (sourceConjugateSubgroup Γ a)) where
  toFun := Quotient.map' (fun x => a * x) (by
    intro x y hxy
    obtain ⟨γ, hγ⟩ := hxy
    refine ⟨(MulAut.conj a).subgroupMap Γ γ, ?_⟩
    change (a * γ.val * a⁻¹) * (a * y) = a * x
    change γ.val * y = x at hγ
    simpa only [mul_assoc, inv_mul_cancel_left] using congrArg (a * ·) hγ)
  invFun := Quotient.map' (fun x => a⁻¹ * x) (by
    intro x y hxy
    obtain ⟨δ, hδ⟩ := hxy
    let e := (MulAut.conj a).subgroupMap Γ
    let γ := e.symm δ
    have he : a * γ.val * a⁻¹ = δ.val := by
      exact congrArg Subtype.val (e.apply_symm_apply δ)
    refine ⟨γ, ?_⟩
    change γ.val * (a⁻¹ * y) = a⁻¹ * x
    change δ.val * y = x at hδ
    calc
      γ.val * (a⁻¹ * y) = a⁻¹ * (δ.val * y) := by rw [← he]; simp only [mul_assoc, inv_mul_cancel_left]
      _ = a⁻¹ * x := congrArg (a⁻¹ * ·) hδ)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | _ x =>
      change Quotient.mk _ (a⁻¹ * (a * x)) = Quotient.mk _ x
      rw [inv_mul_cancel_left]
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | _ x =>
      change Quotient.mk _ (a * (a⁻¹ * x)) = Quotient.mk _ x
      rw [mul_inv_cancel_left]

@[simp] theorem sourceLeftQuotientConjugacy_mk (Γ : Subgroup G) (a x : G) :
    sourceLeftQuotientConjugacy Γ a (Quotient.mk _ x) = Quotient.mk _ (a * x) := rfl

@[simp] theorem sourceLeftQuotientConjugacy_symm_mk (Γ : Subgroup G) (a x : G) :
    (sourceLeftQuotientConjugacy Γ a).symm (Quotient.mk _ x) = Quotient.mk _ (a⁻¹ * x) := rfl

section Measurable
variable [MeasurableSpace G] [MeasurableMul G]

theorem sourceLeftQuotientConjugacy_measurable (Γ : Subgroup G) (a : G) :
    Measurable (sourceLeftQuotientConjugacy Γ a) := by
  intro U hU
  apply measurableSet_quotient.mpr
  change MeasurableSet ((fun x : G => Quotient.mk
    (QuotientGroup.rightRel (sourceConjugateSubgroup Γ a)) (a * x)) ⁻¹' U)
  exact ((measurable_quotient_mk' (s := QuotientGroup.rightRel (sourceConjugateSubgroup Γ a))).comp
    (measurable_const_mul a)) hU

theorem sourceLeftQuotientConjugacy_symm_measurable (Γ : Subgroup G) (a : G) :
    Measurable (sourceLeftQuotientConjugacy Γ a).symm := by
  intro U hU
  apply measurableSet_quotient.mpr
  change MeasurableSet ((fun x : G => Quotient.mk (QuotientGroup.rightRel Γ) (a⁻¹ * x)) ⁻¹' U)
  exact ((measurable_quotient_mk' (s := QuotientGroup.rightRel Γ)).comp
    (measurable_const_mul a⁻¹)) hU

def sourceLeftQuotientConjugacyMeasurableEquiv (Γ : Subgroup G) (a : G) :
    Quotient (QuotientGroup.rightRel Γ) ≃ᵐ
      Quotient (QuotientGroup.rightRel (sourceConjugateSubgroup Γ a)) where
  toEquiv := sourceLeftQuotientConjugacy Γ a
  measurable_toFun := sourceLeftQuotientConjugacy_measurable Γ a
  measurable_invFun := sourceLeftQuotientConjugacy_symm_measurable Γ a

variable (μ : Measure G) [μ.IsMulLeftInvariant]

theorem sourceLeftConjugateDomain (Γ : Subgroup G) (a : G) {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) :
    IsFundamentalDomain (sourceConjugateSubgroup Γ a) ((a * ·) '' F) μ := by
  let e := (MulAut.conj a).subgroupMap Γ
  apply hF.image_of_equiv (Equiv.mulLeft a)
    (measurePreserving_mul_left μ a⁻¹).quasiMeasurePreserving e.symm.toEquiv
  intro γ x
  have he : a * (e.symm γ).val * a⁻¹ = γ.val := by
    exact congrArg Subtype.val (e.apply_symm_apply γ)
  change a * ((e.symm γ).val * x) = γ.val * (a * x)
  rw [← he]
  simp only [mul_assoc, inv_mul_cancel_left]

theorem sourceLeftQuotientConjugacy_measurePreserving (Γ : Subgroup G) [Countable Γ]
    (a : G) {F F' : Set G} (hF : IsFundamentalDomain Γ F μ)
    (hF' : IsFundamentalDomain (sourceConjugateSubgroup Γ a) F' μ) :
    MeasurePreserving (sourceLeftQuotientConjugacy Γ a)
      ((μ.restrict F).map (Quotient.mk (QuotientGroup.rightRel Γ)))
      ((μ.restrict F').map (Quotient.mk (QuotientGroup.rightRel (sourceConjugateSubgroup Γ a)))) := by
  have : Countable (sourceConjugateSubgroup Γ a) :=
    ((MulAut.conj a).subgroupMap Γ).symm.injective.countable
  have hFa := sourceLeftConjugateDomain μ Γ a hF
  have hπ : Measurable (Quotient.mk (QuotientGroup.rightRel Γ)) :=
    measurable_quotient_mk' (s := QuotientGroup.rightRel Γ)
  have hπ' : Measurable (Quotient.mk (QuotientGroup.rightRel (sourceConjugateSubgroup Γ a))) :=
    measurable_quotient_mk' (s := QuotientGroup.rightRel (sourceConjugateSubgroup Γ a))
  refine ⟨sourceLeftQuotientConjugacy_measurable Γ a, ?_⟩
  rw [Measure.map_map (sourceLeftQuotientConjugacy_measurable Γ a) hπ]
  have he : sourceLeftQuotientConjugacy Γ a ∘ Quotient.mk (QuotientGroup.rightRel Γ) =
      Quotient.mk (QuotientGroup.rightRel (sourceConjugateSubgroup Γ a)) ∘ (a * ·) := rfl
  rw [he, ← Measure.map_map hπ' (measurable_const_mul a)]
  have hmp := (measurePreserving_mul_left μ a).restrict_image_emb
    (MeasurableEquiv.mulLeft a).measurableEmbedding F
  rw [hmp.map_eq]
  exact hFa.quotientMeasure_eq μ hF'

end Measurable
end
end ArtinMatthews
