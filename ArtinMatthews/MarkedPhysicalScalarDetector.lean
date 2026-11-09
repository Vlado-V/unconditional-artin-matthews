module

public import ArtinMatthews.MarkedPhysicalScalarCofactor


set_option backward.privateInPublic true
@[expose] public section

/-! Pass from physical cofactor pairs `(m,s),(r,n)` to the actual
scalar endpoint pairs `(m,n),(r,s)`. This is a finite involution
on the original coefficient rectangles. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators ComplexConjugate

def markedPhysicalScalarDetectorTerm (η : ℝ → ℂ) (Y : ℝ)
    (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ)
    (b a : ℕ) (v u : ℕ × ℕ) : ℂ :=
  markedPhysicalScalarCofactorTerm η Y detector α β b a (v.1,u.2) (u.1,v.2)

def markedPhysicalScalarDetectorBlock (S T : Finset ℕ) (η : ℝ → ℂ) (Y : ℝ)
    (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ) (b a : ℕ) : ℂ :=
  ∑ v ∈ S.product T,∑ u ∈ S.product T,markedPhysicalScalarDetectorTerm η Y detector α β b a v u

def markedPhysicalScalarDetectorAbsBlock (S T : Finset ℕ) (η : ℝ → ℂ) (Y : ℝ)
    (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ) (b a : ℕ) : ℝ :=
  ∑ v ∈ S.product T,∑ u ∈ S.product T,‖markedPhysicalScalarDetectorTerm η Y detector α β b a v u‖

theorem markedPhysicalScalarDetectorBlock_norm_le (S T : Finset ℕ)
    (η : ℝ → ℂ) (Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ) (b a : ℕ) :
    ‖markedPhysicalScalarDetectorBlock S T η Y detector α β b a‖ ≤
      markedPhysicalScalarDetectorAbsBlock S T η Y detector α β b a := by
  unfold markedPhysicalScalarDetectorBlock markedPhysicalScalarDetectorAbsBlock
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)

theorem markedPhysicalScalarCofactorTerm_sum (S T : Finset ℕ)
    (η : ℝ → ℂ) (Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ) (b a : ℕ) :
    (∑ v ∈ S.product T,∑ u ∈ S.product T,
      markedPhysicalScalarCofactorTerm η Y detector α β b a v u) =
      markedPhysicalScalarDetectorBlock S T η Y detector α β b a := by
  let R := S.product T
  let F := markedPhysicalScalarCofactorTerm η Y detector α β b a
  let swap : (ℕ×ℕ)×(ℕ×ℕ) → (ℕ×ℕ)×(ℕ×ℕ) :=
    fun p => ((p.1.1,p.2.2),(p.2.1,p.1.2))
  have hI : Function.Involutive swap := fun _ => rfl
  have hmem (p : (ℕ×ℕ)×(ℕ×ℕ)) (hp : p ∈ R.product R) : swap p ∈ R.product R := by
    obtain ⟨hv,hu⟩ := Finset.mem_product.mp hp
    obtain ⟨hm,hs⟩ := Finset.mem_product.mp hv
    obtain ⟨hr,hn⟩ := Finset.mem_product.mp hu
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hm,hn⟩,Finset.mem_product.mpr ⟨hr,hs⟩⟩
  change (∑ v ∈ R,∑ u ∈ R,F v u) = ∑ v ∈ R,∑ u ∈ R,F (v.1,u.2) (u.1,v.2)
  rw [← Finset.sum_product' R R F,← Finset.sum_product' R R (fun v u => F (v.1,u.2) (u.1,v.2))]
  apply Finset.sum_bij (fun p _ => swap p)
  · exact hmem
  · intro p _ q _ hpq
    exact hI.injective hpq
  · intro p hp
    exact ⟨swap p,hmem p hp,hI p⟩
  · intro p _
    rfl

end
end ArtinMatthews
