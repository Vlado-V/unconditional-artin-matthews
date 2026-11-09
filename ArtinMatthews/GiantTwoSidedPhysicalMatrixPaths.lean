module

public import ArtinMatthews.GiantTwoSidedPhysicalFamilyMatrix


set_option backward.privateInPublic true
@[expose] public section

/-! Expanding the physical matrix entries gives the original root-path
statistic with exactly one state mass and both slot averages at each edge. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedExpandedPhysicalMoment_matrix_paths {I J : Type*}
    [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell n : ℕ}
    (patterns : Fin n → Finset I) (C : Fin n → I → J → Finset (Fin k))
    (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i p, GiantTwoSidedPatternCoefficient P (C i p) ell) (roots Z : Finset ℕ) :
    giantTwoSidedExpandedPhysicalMoment patterns C step q ζ K roots Z =
      ∑ s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z,
        (if (s 0).val.1.val ∈ roots ∧ (s (Fin.last n)).val.1.val = (s 0).val.1.val
          then (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) : ℂ) else 0) *
        ∏ i : Fin n, giantTwoSidedPhysicalFamilyMatrix (patterns i) (C i) (step i) q (ζ i) (K i)
          (s i.castSucc) (s i.succ) := by
  let State := GiantTwoSidedEndpointState P (k+ell) Z
  let Choice (i : Fin n) := GiantTwoSidedResidueEdgeChoice (P := P) (patterns i) (C i) ell
  let a : ℂ := giantTwoSidedResidueSlotNormalization (J := J) (k+ell)
  let gate (s : Fin (n+1) → State) : ℂ :=
    if (s 0).val.1.val ∈ roots ∧ (s (Fin.last n)).val.1.val = (s 0).val.1.val then
      (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) : ℂ) else 0
  let F (s : Fin (n+1) → State) (i : Fin n) (c : Choice i) : ℂ :=
    giantTwoSidedPhysicalChoiceCoefficient (step i) q (ζ i) (K i) c (s i.castSucc) (s i.succ)
  have hprod (s : Fin (n+1) → State) :
      (∏ i : Fin n, giantTwoSidedPhysicalFamilyMatrix (patterns i) (C i) (step i) q (ζ i) (K i)
        (s i.castSucc) (s i.succ)) = a^n * ∑ c : (i : Fin n) → Choice i, ∏ i, F s i (c i) := by
    change (∏ i, a * ∑ c : Choice i, F s i c) = _
    rw [Finset.prod_mul_distrib, Fintype.prod_sum]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    _ = a^n * ∑ c : (i : Fin n) → Choice i, ∑ s : Fin (n+1) → State,
          gate s * ∏ i, F s i (c i) := by
      unfold giantTwoSidedExpandedPhysicalMoment giantTwoSidedPhysicalMoment
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : (s 0).val.1.val ∈ roots
      · simp only [h, true_and, ite_true, gate, F, giantTwoSidedPhysicalChoiceCoefficient]
      · simp only [h, false_and, ite_false, zero_mul, gate]
    _ = ∑ s : Fin (n+1) → State, a^n * ∑ c : (i : Fin n) → Choice i,
          gate s * ∏ i, F s i (c i) := by rw [Finset.sum_comm, Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [hprod, ← Finset.mul_sum]
      change _ = gate s * _
      ring

end
end ArtinMatthews
