module

public import ArtinMatthews.GiantTwoSidedRootLabelEquiv
public import ArtinMatthews.GiantTwoSidedRootMargin


set_option backward.privateInPublic true
@[expose] public section

/-! The actual root margin removes the auxiliary finite-slice tests
from the label parametrization. Distinctness, copy/ban compatibility
and every active congruence remain in the exact finite root sum. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

structure GiantTwoSidedRootAdmissible {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    {I : Finset ℕ} (d : GiantTwoSidedRootLabelData (P:=P) k ell n I) : Prop where
  distinct : ∀ v,MarkedPhysicalMarkingDistinct (d.2 v)
  compatible : ∀ i,GiantTwoSidedLabelCompatible (C i)
    (giantTwoSidedPermuteLabels (π i) (d.2 i.castSucc))
    (giantTwoSidedPermuteLabels (τ i) (d.2 i.succ)) (aux i)
  divides : ∀ v j l,(d.2 v j l:ℤ)∣giantTwoSidedRootLabelPosition C π aux step d v

theorem giantCandidateRootAdmissible_iff (k : ℕ) (C₂ : ℝ) {γ : ℝ} (hγ : 0<γ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let n := giantTwoSidedSourceMomentLength x
      ∀ (ell : ℕ) (C : Fin n → S → Finset (Fin k))
        (π τ : Fin n → S → Equiv.Perm (Fin (k+ell)))
        (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ),
        (∀ i,((step i).natAbs:ℝ)≤(Real.log x)^C₂) → ∀ X : ℝ,x^γ≤X →
        ∀ d : GiantTwoSidedRootLabelData (P:=P) k ell n (giantTwoSidedRootInterval X),
          GiantTwoSidedRootLabelCondition C π τ aux step (giantTwoSidedRootSlice X) d ↔
            GiantTwoSidedRootAdmissible C π τ aux step d := by
  filter_upwards [giantCandidateLabelRoot_margin k C₂ hγ] with x hm
  intro S
  dsimp only
  intro ell C π τ aux step hstep X hX d
  constructor
  · intro h
    exact ⟨h.distinct,h.compatible,h.divides⟩
  · intro h
    have hg := hm S ell C d.2 π aux step hstep X hX d.1.val d.1.property
    exact ⟨h.distinct,h.compatible,fun v => (hg v).1.le,fun v => (hg v).2,h.divides⟩

theorem giantCandidatePhysicalPath_root_sum {A : Type*} [AddCommMonoid A]
    (k : ℕ) (C₂ : ℝ) {γ : ℝ} (hγ : 0<γ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let n := giantTwoSidedSourceMomentLength x
      ∀ (ell : ℕ) (C : Fin n → S → Finset (Fin k))
        (π τ : Fin n → S → Equiv.Perm (Fin (k+ell)))
        (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ),
        (∀ i,((step i).natAbs:ℝ)≤(Real.log x)^C₂) → ∀ X : ℝ,x^γ≤X →
        ∀ f : GiantTwoSidedRootLabelData (P:=P) k ell n (giantTwoSidedRootInterval X) → A,
          (∑ s : GiantTwoSidedPhysicalPath C π τ aux step (giantTwoSidedRootInterval X) (giantTwoSidedRootSlice X),
            f (giantTwoSidedRootLabel_encode s).val) =
          ∑ r : ↥(giantTwoSidedRootInterval X),∑ labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell),
            if GiantTwoSidedRootAdmissible C π τ aux step (r,labels) then f (r,labels) else 0 := by
  filter_upwards [giantCandidateRootAdmissible_iff k C₂ hγ] with x hc
  intro S
  dsimp only
  intro ell C π τ aux step hstep X hX f
  rw [giantTwoSidedRootLabel_sum C π τ aux step (giantTwoSidedRootInterval X)
    (giantTwoSidedRootSlice X) (fun d => f d.val)]
  let valid (d : GiantTwoSidedRootLabelData (P:=fun i : S => giantCandidateGroup x i.val) k ell
      (giantTwoSidedSourceMomentLength x) (giantTwoSidedRootInterval X)) :=
    GiantTwoSidedRootLabelCondition C π τ aux step (giantTwoSidedRootSlice X) d
  have hs := Finset.sum_subtype (p:=valid) (F:=inferInstance) (univ.filter valid) (by simp) f
  rw [← hs,sum_filter,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro labels _
  simp only [valid,hc S ell C π τ aux step hstep X hX (r,labels)]

end
end ArtinMatthews
