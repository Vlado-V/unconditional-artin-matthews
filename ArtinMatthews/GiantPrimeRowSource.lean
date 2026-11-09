module

public import ArtinMatthews.GiantPrimeRowCharge
public import ArtinMatthews.GiantSignedTiltedLaw


set_option backward.privateInPublic true
@[expose] public section

/-! Exact identification with the frozen source baseline and tilted prime law. -/

namespace ArtinMatthews
noncomputable section

theorem giantSignedRowBaseline_eq_source (p : ℕ) {n : ℕ} (q : Fin n → ℝ) :
    giantSignedPrimeResidueBaseline p q = giantSignedPrimeBaseline q p := rfl

theorem giantSignedRowBirthAtom_eq_source (P : Finset ℕ) {n : ℕ}
    (q : Fin n → ℝ) (p : P) :
    giantSignedRowBirthAtom (bandReciprocalMass P) p.val q = giantSignedTiltedPrimeLaw P q p := by
  unfold giantSignedRowBirthAtom giantSignedTiltedPrimeLaw markedHarmonicAtom
  rw [giantSignedRowBaseline_eq_source]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

end
end ArtinMatthews
