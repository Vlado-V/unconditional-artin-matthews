module

public import ArtinMatthews.CompactQuotientSection
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum


set_option backward.privateInPublic true
@[expose] public section

/-! Exact quotient periodization by distinct subgroup elements. The
periodized function is proved measurable and integrable, and its
integral unfolds by the actual fundamental-domain Haar normalization. -/
namespace ArtinMatthews.SourcePhysical

open Set MeasureTheory
open scoped Classical ENNReal
noncomputable section
variable {G : Type*} [CommGroup G] (Γ : Subgroup G)

def quotientPeriodize (f : G → ℂ) : G ⧸ Γ → ℂ :=
  Quotient.lift (fun x => ∑' a : Γ.op, f (a • x)) (by
    intro x y h
    have he : (y : G ⧸ Γ) = (x : G ⧸ Γ) := (Quotient.sound h).symm
    let a : Γ.op := ⟨MulOpposite.op (y / x), QuotientGroup.eq_iff_div_mem.mp he⟩
    have ha : a • x = y := by
      change x * (y / x) = y
      rw [mul_comm, div_mul_cancel]
    rw [← ha]
    simpa only [Equiv.coe_mulRight, mul_smul] using
      ((Equiv.mulRight a).tsum_eq (fun g : Γ.op => f (g • x))).symm)

@[simp] theorem quotientPeriodize_mk (f : G → ℂ) (x : G) :
    quotientPeriodize Γ f (x : G ⧸ Γ) = ∑' a : Γ.op, f (a • x) := rfl

variable [MeasurableSpace G] [MeasurableConstSMul Γ.op G] [Countable Γ]

theorem quotientPeriodize_measurable (f : G → ℂ) (hf : Measurable f) :
    Measurable (quotientPeriodize Γ f) :=
  measurable_from_quotient.mpr (Measurable.tsum fun a : Γ.op => hf.comp (measurable_const_smul a))

theorem quotientPeriodize_unfold (ν : Measure G) [SMulInvariantMeasure Γ.op G ν]
    {D : Set G} (hD : IsFundamentalDomain Γ.op D ν)
    (f : G → ℂ) (hfm : Measurable f) (hfi : Integrable f ν) :
    let μ := (ν.restrict D).map (QuotientGroup.mk' Γ)
    Integrable (quotientPeriodize Γ f) μ ∧
      (∫ y, quotientPeriodize Γ f y ∂μ) = ∫ x, f x ∂ν := by
  dsimp only
  have ht (a : Γ.op) : Measurable (fun x : G => f (a • x)) :=
    hfm.comp (measurable_const_smul a)
  have hq : Measurable (QuotientGroup.mk' Γ) := measurable_quotient_mk''
  have hp := quotientPeriodize_measurable Γ f hfm
  have hN : (∑' a : Γ.op, ∫⁻ x in D, ‖f (a • x)‖ₑ ∂ν) ≠ ∞ := by
    rw [← hD.lintegral_eq_tsum'' (fun x => ‖f x‖ₑ)]
    exact hfi.hasFiniteIntegral.ne
  constructor
  · apply (integrable_map_measure hp.aestronglyMeasurable hq.aemeasurable).2
    change Integrable (fun x : G => ∑' a : Γ.op, f (a • x)) (ν.restrict D)
    refine ⟨(Measurable.tsum ht).aestronglyMeasurable, ?_⟩
    change (∫⁻ x in D, ‖∑' a : Γ.op, f (a • x)‖ₑ ∂ν) < ∞
    apply (lintegral_mono fun _ => enorm_tsum_le_tsum_enorm).trans_lt
    rw [lintegral_tsum fun a => (ht a).enorm.aemeasurable]
    exact lt_top_iff_ne_top.mpr hN
  · rw [integral_map hq.aemeasurable hp.aestronglyMeasurable]
    change (∫ x in D, ∑' a : Γ.op, f (a • x) ∂ν) = ∫ x, f x ∂ν
    exact (integral_tsum (fun a => (ht a).aestronglyMeasurable) hN).trans
      (hD.integral_eq_tsum'' f hfi).symm

end
end ArtinMatthews.SourcePhysical
