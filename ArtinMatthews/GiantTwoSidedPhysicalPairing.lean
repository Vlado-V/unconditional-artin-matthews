module

public import ArtinMatthews.GiantTwoSidedPhysicalFamilyMatrix
public import ArtinMatthews.MarkedFiniteCells


set_option backward.privateInPublic true
@[expose] public section

/-! The physical pairing uses the original constant mass. Multiplication
by its square root transports both endpoint vectors to the finite matrix. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {M : ℕ} {Z : Finset ℕ}

def giantTwoSidedPhysicalWeightedPairing
    (A : Matrix (GiantTwoSidedEndpointState P M Z) (GiantTwoSidedEndpointState P M Z) ℂ)
    (f g : GiantTwoSidedEndpointState P M Z → ℂ) : ℂ :=
  (markedPhysicalMass (fun j => bandReciprocalMass (P j)) M : ℂ) * markedMatrixPairing A f g

theorem giantTwoSidedPhysicalWeightedPairing_eq_scaled
    (A : Matrix (GiantTwoSidedEndpointState P M Z) (GiantTwoSidedEndpointState P M Z) ℂ)
    (f g : GiantTwoSidedEndpointState P M Z → ℂ) :
    let σ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) M
    giantTwoSidedPhysicalWeightedPairing A f g =
      markedMatrixPairing A (fun s => (Real.sqrt σ : ℂ)*f s) (fun s => (Real.sqrt σ : ℂ)*g s) := by
  intro σ
  have hσ : 0 ≤ σ := markedPhysicalMass_nonneg _ _ (fun _ =>
    Finset.sum_nonneg (fun _ _ => one_div_nonneg.mpr (Nat.cast_nonneg _)))
  have hs : (Real.sqrt σ : ℂ)^2 = (σ : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hσ]
  change (σ : ℂ)*markedMatrixPairing A f g = _
  simp only [markedMatrixPairing_expansion, Finset.mul_sum, star_mul, Complex.star_def, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [← hs]
  ring

theorem giantTwoSidedPhysicalWeightedPairing_expand {I : Type*} {k ell : ℕ}
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (f g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) :
    giantTwoSidedPhysicalWeightedPairing (giantTwoSidedPhysicalFamilyMatrix patterns C step q ζ K) f g =
      (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) : ℂ)*
      (giantTwoSidedResidueSlotNormalization (J := J) (k+ell) : ℂ)*
        ∑ c : GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell,
          ∑ s, ∑ t, giantTwoSidedPhysicalChoiceCoefficient step q ζ K c s t * star (f s)*g t := by
  let State := GiantTwoSidedEndpointState P (k+ell) Z
  let Choice := GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell
  let a : ℂ := giantTwoSidedResidueSlotNormalization (J := J) (k+ell)
  let F (c : Choice) (s t : State) := giantTwoSidedPhysicalChoiceCoefficient step q ζ K c s t * star (f s)*g t
  have he (s t : State) : giantTwoSidedPhysicalFamilyMatrix patterns C step q ζ K s t * star (f s)*g t =
      a*∑ c : Choice, F c s t := by
    change (a*∑ c : Choice, giantTwoSidedPhysicalChoiceCoefficient step q ζ K c s t)*star (f s)*g t = _
    simp only [F, ← Finset.sum_mul]
    ring
  have hs (s : State) : (∑ t : State, ∑ c : Choice, F c s t) = ∑ c : Choice, ∑ t : State, F c s t :=
    Finset.sum_comm
  have hsum : (∑ s : State, ∑ t : State, ∑ c : Choice, F c s t) =
      ∑ c : Choice, ∑ s : State, ∑ t : State, F c s t := by
    simp only [hs]
    exact Finset.sum_comm
  let σ : ℂ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell)
  calc
    _ = σ*(∑ s : State, ∑ t : State, a*∑ c : Choice, F c s t) := by
      rw [giantTwoSidedPhysicalWeightedPairing, markedMatrixPairing_expansion]
      simp only [he,σ] <;> rfl
    _ = σ*(a*(∑ s : State, ∑ t : State, ∑ c : Choice, F c s t)) := by simp only [Finset.mul_sum]
    _ = _ := by rw [hsum, ← mul_assoc]

end
end ArtinMatthews
