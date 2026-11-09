module

public import ArtinMatthews.MarkedPhysicalCoprimeScalarDetector
public import ArtinMatthews.MarkedPhysicalTypeIIEndpointBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Restricting the input functions to the already-summed scalar
rectangles is exact, including for the literal fixed character factors. -/
namespace ArtinMatthews
noncomputable section

theorem markedPhysicalCoprimeScalarDetectorSum_congr_coefficients
    {J : Type*} [Fintype J] (P : J → Finset ℕ) (S T : Finset ℕ)
    (η : ℝ → ℂ) (Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ)
    {α α' β β' : ℕ → ℂ} (hα : ∀ m∈S,α m=α' m) (hβ : ∀ n∈T,β n=β' n) :
    markedPhysicalCoprimeScalarDetectorSum P S T η Y detector α β =
      markedPhysicalCoprimeScalarDetectorSum P S T η Y detector α' β' := by
  unfold markedPhysicalCoprimeScalarDetectorSum markedPhysicalScalarDetectorBlock
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  obtain ⟨hvm,hvn⟩ := Finset.mem_product.mp hv
  obtain ⟨hum,hun⟩ := Finset.mem_product.mp hu
  simp only [markedPhysicalScalarDetectorTerm,markedPhysicalScalarCofactorTerm,
    hα _ hvm,hα _ hum,hβ _ hvn,hβ _ hun]

theorem markedPhysicalCoprimeScalarDetectorSum_restricted_coefficients
    {J : Type*} [Fintype J] (P : J → Finset ℕ) (S T : Finset ℕ)
    (η : ℝ → ℂ) (Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ)
    (W modulation : ℝ) (β ξ : ℕ → ℂ) :
    markedPhysicalCoprimeScalarDetectorSum P S T η Y detector
      (fun n => ξ n*markedMajorRestrictedCoefficient W modulation S n)
      (fun n => ξ n*markedPhysicalRestrictedBeta T β n)=
    markedPhysicalCoprimeScalarDetectorSum P S T η Y detector
      (fun n => ξ n*markedMajorCenteredCoefficient W modulation n) (fun n => ξ n*β n) := by
  apply markedPhysicalCoprimeScalarDetectorSum_congr_coefficients
  · intro m hm
    simp only [markedMajorRestrictedCoefficient,ite_eq_left hm]
  · intro n hn
    simp only [markedPhysicalRestrictedBeta,ite_eq_left hn]

end
end ArtinMatthews
