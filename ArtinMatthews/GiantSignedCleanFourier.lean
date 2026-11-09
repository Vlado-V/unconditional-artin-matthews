module

public import ArtinMatthews.GiantSignedCleanFiber
public import ArtinMatthews.GiantSignedFourierLinear


set_option backward.privateInPublic true
@[expose] public section

/-! The actual clean operator is diagonalized by the residue characters.
The auxiliary and fresh laws, derivative lift, and both slot averages are retained. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedFourier_slotAverage
    {G J : Type*} [AddCommGroup G] [Fintype G] [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ}
    (f : G → MarkedPhysicalMarking P M → ℂ) (χ : AddChar G ℂ)
    (a : MarkedPhysicalMarking P M) :
    giantSignedFourier (fun x => idealSlotAverage (f x) a) χ =
      idealSlotAverage (fun b => giantSignedFourier (fun x => f x b) χ) a := by
  classical
  unfold idealSlotAverage
  rw [giantSignedFourier_const_mul, giantSignedFourier_sum]

theorem giantSignedFourier_phase_translate
    {G : Type*} [AddCommGroup G] [Fintype G]
    (c : ℂ) (Θ : ℝ) (D : ℕ) (u : G) (f : G → ℂ) (χ : AddChar G ℂ) :
    giantSignedFourier (fun x => c * idealAdditivePhase Θ D * f (x + D • u)) χ =
      c * idealAdditivePhase (Θ + giantSignedCharacterPhase χ u) D *
        giantSignedFourier f χ := by
  rw [giantSignedFourier_const_mul, giantSignedFourier_translate]
  rw [mul_assoc c, ← mul_assoc (idealAdditivePhase Θ D),
    giantSignedCharacterPhase_idealPhase]
  ring

theorem giantSignedCleanFiberPattern_fourier
    {G J : Type*} [AddCommGroup G] [Fintype G] [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, P j → ℝ) (C : J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (u : G)
    (f : G → MarkedPhysicalMarking P (k+ell) → ℂ)
    (χ : AddChar G ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    giantSignedFourier (fun x =>
      giantSignedCleanFiberPattern freshLaw auxLaw C Θ ζ K u f x a) χ =
      idealPatternApplyWithLaws freshLaw auxLaw C
        (Θ + giantSignedCharacterPhase χ u) ζ K
        (fun b => giantSignedFourier (fun x => f x b) χ) a := by
  classical
  unfold giantSignedCleanFiberPattern idealPatternApplyWithLaws
  rw [giantSignedFourier_sum]
  apply Finset.sum_congr rfl
  intro aux _
  rw [giantSignedFourier_const_mul, giantSignedFourier_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : IdealCopied C a b
  · simp only [h, ite_true]
    exact giantSignedFourier_phase_translate _ Θ _ u (fun x => f x b) χ
  · simp [h, giantSignedFourier]

theorem giantSignedCleanFiberApply_fourier
    {I G J : Type*} [AddCommGroup G] [Fintype G] [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ ν, GiantTwoSidedPatternCoefficient P (C ν) ell) (u : G)
    (f : G → MarkedPhysicalMarking P (k+ell) → ℂ)
    (χ : AddChar G ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    giantSignedFourier (fun x =>
      giantSignedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u f x a) χ =
      idealOperatorWithLaws freshLaw auxLaw patterns C
        (Θ + giantSignedCharacterPhase χ u) ζ K
        (fun b => giantSignedFourier (fun x => f x b) χ) a := by
  classical
  unfold giantSignedCleanFiberApply idealOperatorWithLaws
  rw [giantSignedFourier_slotAverage]
  congr 1
  funext b
  rw [giantSignedFourier_sum]
  apply Finset.sum_congr rfl
  intro ν hν
  rw [giantSignedCleanFiberPattern_fourier]
  congr 1
  funext c
  exact giantSignedFourier_slotAverage f χ c

theorem giantSignedCleanFiberApply_energy
    {I G J : Type*} [AddCommGroup G] [Fintype G] [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (activeMass : MarkedPhysicalMarking P (k+ell) → ℝ)
    (freshLaw auxLaw : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ U : ℝ)
    (K : ∀ ν, GiantTwoSidedPatternCoefficient P (C ν) ell) (u : G)
    (hIdeal : ∀ θ (h : MarkedPhysicalMarking P (k+ell) → ℂ),
      (∑ a, activeMass a *
        ‖idealOperatorWithLaws freshLaw auxLaw patterns C θ ζ K h a‖ ^ 2) ≤
          U ^ 2 * ∑ a, activeMass a * ‖h a‖ ^ 2)
    (f : G → MarkedPhysicalMarking P (k+ell) → ℂ) :
    (∑ x, ∑ a, activeMass a *
      ‖giantSignedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u f x a‖ ^ 2) ≤
        U ^ 2 * ∑ x, ∑ a, activeMass a * ‖f x a‖ ^ 2 := by
  apply giantSignedFourier_energy_bound activeMass U f
  intro χ
  simp_rw [giantSignedCleanFiberApply_fourier]
  exact hIdeal (Θ + giantSignedCharacterPhase χ u) _

theorem giantSignedFourier_symmetric
    {G J : Type*} [AddCommGroup G] [Fintype G]
    {P : J → Finset ℕ} {M : ℕ}
    (f : G → MarkedPhysicalMarking P M → ℂ)
    (hf : ∀ x, IdealSymmetric (f x)) (χ : AddChar G ℂ) :
    IdealSymmetric (fun a => giantSignedFourier (fun x => f x a) χ) := by
  intro π a
  unfold giantSignedFourier
  simp_rw [hf _ π a]

theorem giantSignedCleanFiberApply_energy_symmetric
    {I G J : Type*} [AddCommGroup G] [Fintype G] [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (activeMass : MarkedPhysicalMarking P (k+ell) → ℝ)
    (freshLaw auxLaw : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ U : ℝ)
    (K : ∀ ν, GiantTwoSidedPatternCoefficient P (C ν) ell) (u : G)
    (hIdeal : ∀ θ (h : MarkedPhysicalMarking P (k+ell) → ℂ), IdealSymmetric h →
      (∑ a, activeMass a *
        ‖idealOperatorWithLaws freshLaw auxLaw patterns C θ ζ K h a‖ ^ 2) ≤
          U ^ 2 * ∑ a, activeMass a * ‖h a‖ ^ 2)
    (f : G → MarkedPhysicalMarking P (k+ell) → ℂ)
    (hf : ∀ x, IdealSymmetric (f x)) :
    (∑ x, ∑ a, activeMass a *
      ‖giantSignedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u f x a‖ ^ 2) ≤
        U ^ 2 * ∑ x, ∑ a, activeMass a * ‖f x a‖ ^ 2 := by
  apply giantSignedFourier_energy_bound activeMass U f
  intro χ
  simp_rw [giantSignedCleanFiberApply_fourier]
  exact hIdeal (Θ + giantSignedCharacterPhase χ u) _ (giantSignedFourier_symmetric f hf χ)

end
end ArtinMatthews
