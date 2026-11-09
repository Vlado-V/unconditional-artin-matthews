module

public import ArtinMatthews.SpectralOrbitalWeylKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The actual positive-c geometric fibre is its period-N double-coset
Kloosterman phase sum times the proved residue-independent Weyl integral. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff BigOperators

namespace ArtinMatthews

theorem gamma0PositiveGeometricFibre_eq_kloosterman (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (m n : ℤ)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    (∑ᶠ M : gamma0CuspMatrixFibre N r s c, compactPoincareGeometricKernel
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) m ρ hρ hcρ hpρ)
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n η hη hcη hpη) M.val) =
      gamma0PeriodKloostermanSum N r s c m n *
        cuspWeylOrbitalKernel N m n ρ η (c : ℝ) (by exact_mod_cast NeZero.ne c) := by
  rw [compactPoincareGeometricKernel_double_coset_sum N r s c]
  calc
    _ = ∑ R : gamma0CuspReducedMatrix N r s c,
        cuspUnwindowedOrbitalKernel N m n ρ η R.val := by
      apply Finset.sum_congr rfl
      intro R _
      exact cuspOrbitalIntegral_eq_unwindowed N m n ρ η hρ hη hcρ hcη hpρ hpη R.val
        (by rw [R.property.2.1]; exact_mod_cast NeZero.ne c)
    _ = ∑ R : gamma0CuspReducedMatrix N r s c,
        cuspGeometricPhase N m n (c : ℤ) R.val *
          cuspWeylOrbitalKernel N m n ρ η (c : ℝ) (by exact_mod_cast NeZero.ne c) := by
      apply Finset.sum_congr rfl
      intro R _
      exact cuspUnwindowedOrbitalKernel_bruhat N m n ρ η R.val
        (by exact_mod_cast NeZero.ne c) R.property.2.1
    _ = _ := by rw [← Finset.sum_mul]; rfl

end ArtinMatthews
