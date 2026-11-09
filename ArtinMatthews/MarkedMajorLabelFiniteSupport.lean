module

public import ArtinMatthews.MarkedMajorLabelSupportedEndpoint


set_option backward.privateInPublic true
@[expose] public section

/-! Exact zero-cutoff removal for the original finite source, with an arbitrary
bilateral kernel. No analytic or support bounds are needed. -/
namespace ArtinMatthews
open Finset
noncomputable section

theorem markedMajorSupported_weighted_sum {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ) (K : ℕ×(ℕ×ℕ) → ℂ) :
    (∑ z ∈ markedMajorSupportedTripleSet bands cutoff Y u v l r,
      markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β z*K z) =
    ∑ z ∈ markedMajorLabelTripleSet bands u v l r,
      markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β z*K z := by
  classical
  apply sum_subset (filter_subset _ _)
  intro z hz hznot
  have hz0 : cutoff ((z.1:ℝ)/Y)=0 := by
    by_contra h
    exact hznot (mem_filter.mpr ⟨hz,h⟩)
  simp only [markedMajorLabelTripleCoefficient,markedMajorLabelWeight,hz0,zero_mul]

theorem markedMajorSupported_conjugate_weighted_sum {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ) (K : ℕ×(ℕ×ℕ) → ℂ) :
    (∑ z ∈ markedMajorSupportedTripleSet bands cutoff Y u v l r,
      markedMajorLabelConjugateTripleCoefficient bands cutoff χb θ Y χ W modulation β z*K z) =
    ∑ z ∈ markedMajorLabelTripleSet bands u v l r,
      markedMajorLabelConjugateTripleCoefficient bands cutoff χb θ Y χ W modulation β z*K z := by
  simp only [markedMajorLabelConjugateTripleCoefficient_eq]
  exact markedMajorSupported_weighted_sum bands cutoff χb θ Y χ W (-modulation) u v l r β K

theorem markedMajorSupported_bilateral_sum {J J' : Type*} [Fintype J] [Fintype J']
    (bands : J → Finset ℕ) (bands' : J' → Finset ℕ) (cutoff : ℝ → ℂ)
    {k q k' q' : ℕ} (χb : DirichletCharacter ℂ k) (χb' : DirichletCharacter ℂ k')
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (θ θ' Y W modulation modulation' u v u' v' : ℝ)
    (l r l' r' : ℕ) (β β' : ℕ → ℂ) (K : (ℕ×(ℕ×ℕ)) → (ℕ×(ℕ×ℕ)) → ℂ) :
    (∑ z ∈ markedMajorSupportedTripleSet bands cutoff Y u v l r,
      ∑ z' ∈ markedMajorSupportedTripleSet bands' cutoff Y u' v' l' r',
      (markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β z*
       markedMajorLabelConjugateTripleCoefficient bands' cutoff χb' θ' Y χ' W modulation' β' z')*K z z') =
    ∑ z ∈ markedMajorLabelTripleSet bands u v l r,
      ∑ z' ∈ markedMajorLabelTripleSet bands' u' v' l' r',
      (markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β z*
       markedMajorLabelConjugateTripleCoefficient bands' cutoff χb' θ' Y χ' W modulation' β' z')*K z z' := by
  simp_rw [mul_assoc,← mul_sum]
  simp_rw [markedMajorSupported_conjugate_weighted_sum]
  exact markedMajorSupported_weighted_sum bands cutoff χb θ Y χ W modulation u v l r β _

end
end ArtinMatthews
