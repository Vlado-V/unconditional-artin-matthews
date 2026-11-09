module

public import ArtinMatthews.MarkedMajorArcPaperSource
public import Mathlib.Logic.Equiv.Option


set_option backward.privateInPublic true
@[expose] public section

/-! Selecting a distinguished prime band preserves the actual label set,
normalizer and literal sixfold determinant sum exactly. -/
namespace ArtinMatthews
open Finset

 theorem markedMajorLabelSet_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (P : J → Finset ℕ) :
    markedMajorLabelSet (fun i => P (e i))=markedMajorLabelSet P := by
  classical
  let E := Equiv.piCongrLeft (fun j => ↥(P j)) e
  have hp (t : (i : I) → ↥(P (e i))) :
      markedPrimeBandProduct P (E t)=markedPrimeBandProduct (fun i => P (e i)) t := by
    unfold markedPrimeBandProduct
    rw [← e.prod_comp (fun j => (E t j:ℕ))]
    apply prod_congr rfl
    intro i _
    rw [Equiv.piCongrLeft_apply_apply]
  ext n
  simp only [markedMajorLabelSet,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨E t,hp t⟩
  · rintro ⟨t,rfl⟩
    refine ⟨E.symm t,?_⟩
    rw [← hp,E.apply_symm_apply]

 theorem markedMajorLabelMass_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (P : J → Finset ℕ) :
    markedMajorLabelMass (fun i => P (e i))=markedMajorLabelMass P :=
  e.prod_comp (fun j => (bandReciprocalMass (P j))⁻¹)

 theorem markedMajorDeterminantPaperSum_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (P : J → Finset ℕ) (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ) :
    markedMajorDeterminantPaperSum (fun i => P (e i)) cutoff ψ Q Y W modulation u v l r β =
      markedMajorDeterminantPaperSum P cutoff ψ Q Y W modulation u v l r β := by
  simp only [markedMajorDeterminantPaperSum,markedMajorLabelSet_reindex,markedMajorLabelMass_reindex]

end ArtinMatthews
