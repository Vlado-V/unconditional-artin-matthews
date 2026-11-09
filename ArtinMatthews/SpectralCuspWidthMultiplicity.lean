module

public import ArtinMatthews.SpectralCuspWidthRefinement


set_option backward.privateInPublic true
@[expose] public section

/-! Every individual primitive-width class has exactly the same explicitly
indexed number of common-period N classes above it. -/

noncomputable section
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0CuspWidthReduction (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : ℕ) [NeZero c] (M : gamma0CuspReducedMatrix N r s c) :
    gamma0TrueWidthReducedMatrix N r s c :=
  ((gamma0CuspWidthRefinementEquiv N r s c).symm M).1

def gamma0CuspWidthReductionFibreEquiv (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c]
    (R : gamma0TrueWidthReducedMatrix N r s c) :
    (Fin (gamma0CuspFrequencyStep N s) × Fin (gamma0CuspFrequencyStep N r)) ≃
      {M : gamma0CuspReducedMatrix N r s c // gamma0CuspWidthReduction N r s c M = R} where
  toFun p := ⟨gamma0CuspWidthRefinementEquiv N r s c (R,p),by
    simp only [gamma0CuspWidthReduction,Equiv.symm_apply_apply]⟩
  invFun M := ((gamma0CuspWidthRefinementEquiv N r s c).symm M.val).2
  left_inv p := by simp only [Equiv.symm_apply_apply]
  right_inv M := by
    apply Subtype.ext
    apply (gamma0CuspWidthRefinementEquiv N r s c).symm.injective
    simp only [Equiv.symm_apply_apply]
    exact Prod.ext M.property.symm rfl

theorem gamma0CuspWidthReduction_fibre_card (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c]
    (R : gamma0TrueWidthReducedMatrix N r s c) :
    Nat.card {M : gamma0CuspReducedMatrix N r s c // gamma0CuspWidthReduction N r s c M = R} =
      gamma0CuspFrequencyStep N s * gamma0CuspFrequencyStep N r := by
  rw [← Nat.card_congr (gamma0CuspWidthReductionFibreEquiv N r s c R)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fin]

theorem gamma0CuspWidthReduction_surjective (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Function.Surjective (gamma0CuspWidthReduction N r s c) := by
  intro R
  let a : Fin (gamma0CuspFrequencyStep N s) := ⟨0,gamma0CuspFrequencyStep_pos N s⟩
  let b : Fin (gamma0CuspFrequencyStep N r) := ⟨0,gamma0CuspFrequencyStep_pos N r⟩
  exact ⟨(gamma0CuspWidthReductionFibreEquiv N r s c R (a,b)).val,
    (gamma0CuspWidthReductionFibreEquiv N r s c R (a,b)).property⟩

end ArtinMatthews
