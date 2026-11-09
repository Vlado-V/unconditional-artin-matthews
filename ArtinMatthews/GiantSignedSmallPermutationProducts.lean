module

public import ArtinMatthews.GiantSignedSmallOmissionPermutations
public import Mathlib.Algebra.BigOperators.Fin


set_option backward.privateInPublic true
@[expose] public section

/-! The copied small product in the original source-slot average is the
complement of the omitted suffix image. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

section Products
variable {S : Type*} [Fintype S] {P : S → Finset ℕ} {kCopy ell : ℕ}

def giantSignedSmallPermutationCopiedProduct (a : MarkedPhysicalMarking P (kCopy + ell))
    (σ : (g : S) → Equiv.Perm (Fin (kCopy + ell))) : ℕ :=
  ∏ g, ∏ i : Fin kCopy, (a g (σ g (Fin.castAdd ell i)) : ℕ)

theorem giantSignedSmallPermutationOmittedProduct (a : MarkedPhysicalMarking P (kCopy + ell))
    (σ : (g : S) → Equiv.Perm (Fin (kCopy + ell))) :
    giantSignedSmallOmittedProduct a (giantSignedSmallPermutationOmission kCopy ell σ) =
      ∏ g, ∏ i : Fin ell, (a g (σ g (Fin.natAdd kCopy i)) : ℕ) := by
  simp only [giantSignedSmallOmittedProduct, giantSignedSmallPermutationOmission,
    giantSignedSmallOmissionSuffix, Finset.prod_map, Function.Embedding.coeFn_mk,
    Equiv.toEmbedding_apply]

theorem giantSignedSmallPermutationCopied_mul_omitted
    (a : MarkedPhysicalMarking P (kCopy + ell))
    (σ : (g : S) → Equiv.Perm (Fin (kCopy + ell))) :
    giantSignedSmallPermutationCopiedProduct a σ *
      giantSignedSmallOmittedProduct a (giantSignedSmallPermutationOmission kCopy ell σ) =
        markedPhysicalMarkingProduct a := by
  rw [giantSignedSmallPermutationOmittedProduct, giantSignedSmallPermutationCopiedProduct,
    ← Finset.prod_mul_distrib]
  unfold markedPhysicalMarkingProduct
  apply Finset.prod_congr rfl
  intro g _
  rw [← Fin.prod_univ_add (fun i : Fin (kCopy + ell) => (a g (σ g i) : ℕ))]
  exact Equiv.prod_comp (σ g) (fun i => (a g i : ℕ))

theorem giantSignedSmallPermutationCopied_eq (hP : ∀ g q, q ∈ P g → q.Prime)
    (a : MarkedPhysicalMarking P (kCopy + ell))
    (σ : (g : S) → Equiv.Perm (Fin (kCopy + ell))) :
    giantSignedSmallPermutationCopiedProduct a σ =
      giantSignedSmallCopiedProduct a (giantSignedSmallPermutationOmission kCopy ell σ) := by
  apply mul_right_cancel₀
    (giantSignedSmallOmittedProduct_pos hP a (giantSignedSmallPermutationOmission kCopy ell σ)).ne'
  rw [giantSignedSmallPermutationCopied_mul_omitted, giantSignedSmallCopied_mul_omitted]

end Products
end
end ArtinMatthews
