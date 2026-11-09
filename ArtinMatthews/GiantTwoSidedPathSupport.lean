module

public import ArtinMatthews.GiantTwoSidedRootLabelData


set_option backward.privateInPublic true
@[expose] public section

/-! Restricting the original finite path sum to supported edges is
exact: every excluded path has a zero factor in the actual kernel. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedPhysicalPath_product_zero {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell)
    {Z : Finset ℕ} (s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z)
    (h : ¬∀ i,GiantTwoSidedPatternCondition (C i) (step i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)) :
    (∏ i : Fin n,giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i) (K i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i))=0 := by
  push Not at h
  obtain ⟨i,hi⟩ := h
  apply prod_eq_zero (mem_univ i)
  exact ite_eq_right hi

theorem giantTwoSidedPhysicalPath_sum_support {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell)
    (I Z : Finset ℕ) (F : (Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z) → ℂ) :
    (∑ s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z,
      if (s 0).val.1.val∈I then F s*
        (∏ i : Fin n,giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i) (K i)
          (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
          (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)) else 0) =
      ∑ s : GiantTwoSidedPhysicalPath C π τ aux step I Z,F s.val*
        (∏ i : Fin n,giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i) (K i)
          (giantTwoSidedEndpointPermute (π i) (s.val i.castSucc))
          (giantTwoSidedEndpointPermute (τ i) (s.val i.succ)) (aux i)) := by
  let g (s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z) := F s*
    ∏ i : Fin n,giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i) (K i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)
  let valid := GiantTwoSidedPhysicalPathCondition C π τ aux step I Z
  have hs := Finset.sum_subtype (p:=valid) (F:=inferInstance) (univ.filter valid) (by simp) g
  rw [← hs,sum_filter]
  apply sum_congr rfl
  intro s _
  have hc : valid s ↔ (s 0).val.1.val∈I ∧ ∀ i,GiantTwoSidedPatternCondition (C i) (step i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i) :=
    ⟨fun h => ⟨h.root_mem,h.edges⟩,fun h => ⟨h.1,h.2⟩⟩
  change (if _ then g s else 0)=(if valid s then g s else 0)
  rw [hc]
  by_cases hr : (s 0).val.1.val∈I
  · by_cases he : ∀ i,GiantTwoSidedPatternCondition (C i) (step i)
        (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
        (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)
    · rw [ite_eq_left hr,ite_eq_left (And.intro hr he)]
    · have hg : g s=0 := by
        dsimp only [g]
        rw [giantTwoSidedPhysicalPath_product_zero π τ aux step q ζ K s he,mul_zero]
      rw [ite_eq_left hr,ite_eq_right (fun hh => he hh.2),hg]
  · rw [ite_eq_right hr,ite_eq_right (fun hh => hr hh.1)]

end
end ArtinMatthews
