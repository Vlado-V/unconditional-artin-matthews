module

public import ArtinMatthews.SpectralCuspEisensteinZeroRows
public import ArtinMatthews.SpectralGeometricSignSectors


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped MatrixGroups Classical
noncomputable section

/-- An actual correspondence between inequivalent cusps has nonzero lower entry. -/
theorem gamma0CuspCorrespondence_lower_ne_zero_of_inequivalent
    (N : ℕ) (r s : SL(2, ℤ)) (h : ¬ gamma0EisensteinCuspsEquivalent N r s)
    (M : gamma0CuspCorrespondence N r s) : M.val 1 0 ≠ 0 := by
  intro hM
  exact h ((gamma0EisensteinCuspsEquivalent_iff N r s).mpr ⟨M, hM⟩)

/-- The literal zero-lower-entry matrix fibre is empty for inequivalent cusps. -/
theorem gamma0ZeroGeometricFibre_isEmpty_of_inequivalent
    (N : ℕ) (r s : SL(2, ℤ)) (h : ¬ gamma0EisensteinCuspsEquivalent N r s) :
    IsEmpty {M : gamma0CuspCorrespondence N r s // M.val 1 0 = 0} :=
  ⟨fun M => gamma0CuspCorrespondence_lower_ne_zero_of_inequivalent N r s h M.val M.property⟩

/-- The zero sector of the actual correspondence has empty support. -/
theorem gamma0ZeroGeometricFibre_eq_empty_of_inequivalent
    (N : ℕ) (r s : SL(2, ℤ)) (h : ¬ gamma0EisensteinCuspsEquivalent N r s) :
    {M : gamma0CuspCorrespondence N r s | M.val 1 0 = 0} = ∅ := by
  ext M
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact gamma0CuspCorrespondence_lower_ne_zero_of_inequivalent N r s h M

/-- The literal zero geometric sum vanishes for inequivalent Gamma0 cusps. -/
theorem gamma0ZeroGeometricSum_eq_zero_of_inequivalent
    (N : ℕ) (r s : SL(2, ℤ)) (h : ¬ gamma0EisensteinCuspsEquivalent N r s)
    (ψ φ : h2SmoothCompactSeeds) : gamma0ZeroGeometricSum N r s ψ φ = 0 := by
  unfold gamma0ZeroGeometricSum
  have hz (M : gamma0CuspCorrespondence N r s) :
      (if M.val 1 0 = 0 then compactPoincareGeometricKernel ψ φ M.val else 0) = 0 := by
    rw [ite_eq_right (gamma0CuspCorrespondence_lower_ne_zero_of_inequivalent N r s h M)]
  simp only [hz, finsum_zero]

end
end ArtinMatthews
