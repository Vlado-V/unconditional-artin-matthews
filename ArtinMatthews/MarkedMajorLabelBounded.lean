module

public import ArtinMatthews.MarkedMajorLabelMeanConjugate
public import ArtinMatthews.MarkedMajorEnergyBounded


set_option backward.privateInPublic true
@[expose] public section

/-! Nonquantitative global bounds for the finite actual endpoint sums.
These witnesses justify weighted integration; their size is never used. -/
namespace ArtinMatthews
open Finset

theorem markedMajorLabelPolynomial_bounded {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) :
    ∃ B : ℝ,∀ t : ℝ,‖markedMajorLabelPolynomial bands cutoff χb θ Y t‖ ≤ B := by
  let a := fun (s : ℕ) => cutoff ((s:ℝ)/Y)*Complex.exp (((-2*Real.pi*θ*(s:ℝ)/Y:ℝ):ℂ)*Complex.I)*
    (markedMajorLabelMass bands:ℂ)*χb s
  refine ⟨‖(Y:ℂ)⁻¹‖*∑ s ∈ markedMajorLabelSet bands,‖a s‖,?_⟩
  intro t
  unfold markedMajorLabelPolynomial
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact markedNaturalPolynomial_norm_le (markedMajorLabelSet bands) a t

theorem markedMajorLabelEndpoint_bounded {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ) :
    ∃ B : ℝ,∀ t : ℝ,‖markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β t‖ ≤ B := by
  obtain ⟨A,hA⟩ := markedMajorLabelPolynomial_bounded bands cutoff χb θ Y
  obtain ⟨B,hB⟩ := marked_centered_sum_bounded χ W modulation H u v
  obtain ⟨C,hC⟩ := marked_dyadic_sum_bounded l r U β
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨A*B*C,?_⟩
  intro t
  unfold markedMajorLabelEndpoint
  simp only [norm_mul]
  exact mul_le_mul (mul_le_mul (hA t) (hB t) (norm_nonneg _) hA0)
    (hC t) (norm_nonneg _) (mul_nonneg hA0 hB0)

theorem markedMajorLabelConjugateEndpoint_bounded {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ) :
    ∃ B : ℝ,∀ t : ℝ,‖markedMajorLabelConjugateEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β t‖ ≤ B := by
  simp only [markedMajorLabelConjugateEndpoint_eq]
  exact markedMajorLabelEndpoint_bounded bands cutoff χb θ Y χ W (-modulation) H u v U l r β

theorem markedMajorLabelConjugateEndpoint_continuous {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ) :
    Continuous (markedMajorLabelConjugateEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β) := by
  have he : markedMajorLabelConjugateEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β =
      markedMajorLabelEndpoint bands cutoff χb θ Y χ W (-modulation) H u v U l r β := by
    funext t
    exact markedMajorLabelConjugateEndpoint_eq bands cutoff χb θ Y χ W modulation H u v U l r β t
  rw [he]
  exact markedMajorLabelEndpoint_continuous bands cutoff χb θ Y χ W (-modulation) H u v U l r β

end ArtinMatthews
