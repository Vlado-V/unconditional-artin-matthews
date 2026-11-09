module

public import ArtinMatthews.MarkedPhysicalCoprimeScalarDetector
public import ArtinMatthews.MarkedTypeIISharedLabelSupport


set_option backward.privateInPublic true
@[expose] public section

/-! The original cutoff restricts the absolute detector mass to the
literal visible dyad, with no restriction on the sign of the detector. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalCoprimeDyadPairs {J : Type*} [Fintype J] (P : J → Finset ℕ) (Y : ℝ) : Finset (ℕ×ℕ) :=
  ((markedTypeIIDyadLabels P Y).product (markedTypeIIDyadLabels P Y)).filter
    (fun z => z.1.Coprime z.2)

theorem markedPhysicalCoprimeScalarDetectorAbsMass_dyad
    {J : Type*} [Fintype J] (P : J → Finset ℕ) (S T : Finset ℕ) (η : ℝ → ℂ) {Y : ℝ}
    (hY : 0 < Y) (hη : Function.support η ⊆ Set.Icc 1 4)
    (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ) :
    markedPhysicalCoprimeScalarDetectorAbsMass P S T η Y detector α β =
      (markedMajorLabelMass P)^2*
        ∑ z ∈ markedPhysicalCoprimeDyadPairs P Y,
          markedPhysicalScalarDetectorAbsBlock S T η Y detector α β z.1 z.2 := by
  unfold markedPhysicalCoprimeScalarDetectorAbsMass
  congr 1
  symm
  apply Finset.sum_subset
  · intro z hz
    obtain ⟨hbox,hcop⟩ := Finset.mem_filter.mp hz
    obtain ⟨hb,ha⟩ := Finset.mem_product.mp hbox
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hb).1,(Finset.mem_filter.mp ha).1⟩,hcop⟩
  · intro z hz hnot
    obtain ⟨hbox,hcop⟩ := Finset.mem_filter.mp hz
    obtain ⟨hb,ha⟩ := Finset.mem_product.mp hbox
    have hd {b : ℕ} (hb : b ∈ markedMajorLabelSet P) (hne : η ((b:ℝ)/Y) ≠ 0) :
        b ∈ markedTypeIIDyadLabels P Y := by
      exact Finset.mem_filter.mpr ⟨hb,markedPhysical_cutoff_label_range hη hY hne⟩
    by_cases h₁ : η ((z.1:ℝ)/Y)=0
    · simp only [markedPhysicalScalarDetectorAbsBlock,markedPhysicalScalarDetectorTerm,
        markedPhysicalScalarCofactorTerm,h₁,zero_mul,norm_zero,Finset.sum_const_zero]
    · have h₂ : η ((z.2:ℝ)/Y)=0 := by
        by_contra h₂
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hd hb h₁,hd ha h₂⟩,hcop⟩)
      simp only [markedPhysicalScalarDetectorAbsBlock,markedPhysicalScalarDetectorTerm,
        markedPhysicalScalarCofactorTerm,h₂,mul_zero,zero_mul,norm_zero,Finset.sum_const_zero]

end
end ArtinMatthews
