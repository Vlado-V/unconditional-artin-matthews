module

public import ArtinMatthews.SpectralCuspDoubleCosetRepresentatives
public import ArtinMatthews.SpectralPoincareGeometricKernel


set_option backward.privateInPublic true
@[expose] public section

/-! Exact fixed-positive-modulus reindexing of the actual compact geometric
kernel, retaining the common period N and both integer translation factors. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace Pointwise BigOperators

namespace ArtinMatthews

theorem compactPoincareGeometricKernel_all_hasFiniteSupport (ψ φ : h2SmoothCompactSeeds) :
    Function.HasFiniteSupport (compactPoincareGeometricKernel ψ φ) := by
  apply (integer_compact_translates_finite ψ.val.hasCompactSupport φ.val.hasCompactSupport).subset
  intro M hM
  by_contra hnot
  apply hM
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  simp only [Pi.zero_apply]
  by_cases hz : ψ.val z = 0
  · rw [hz,inner_zero_left]
  have hφ : φ.val (M • z) = 0 := by
    by_contra hφ
    exact hnot ⟨M • z, ⟨⟨z,subset_tsupport _ hz,rfl⟩,subset_tsupport _ hφ⟩⟩
  rw [hφ,inner_zero_right]

theorem compactPoincareDoubleCoset_hasFiniteSupport (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (ψ φ : h2SmoothCompactSeeds) :
    Function.HasFiniteSupport (fun p : gamma0CuspReducedMatrix N r s c × ℤ × ℤ =>
      compactPoincareGeometricKernel ψ φ (gamma0CuspDoubleCosetExpand N r s c p).val) := by
  apply Function.HasFiniteSupport.fun_comp_of_injective
    (g := fun p : gamma0CuspReducedMatrix N r s c × ℤ × ℤ =>
      (gamma0CuspDoubleCosetExpand N r s c p).val)
  · exact Subtype.val_injective.comp (gamma0CuspDoubleCosetExpand_injective N r s c)
  · exact compactPoincareGeometricKernel_all_hasFiniteSupport ψ φ

theorem compactPoincareGeometricKernel_double_coset_sum (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (ψ φ : h2SmoothCompactSeeds) :
    (∑ᶠ M : gamma0CuspMatrixFibre N r s c, compactPoincareGeometricKernel ψ φ M.val) =
      ∑ R : gamma0CuspReducedMatrix N r s c, ∑ᶠ p : ℤ × ℤ,
        compactPoincareGeometricKernel ψ φ
          (integerTranslation ((N : ℤ) * p.1) * R.val * integerTranslation ((N : ℤ) * p.2)) := by
  rw [← gamma0CuspDoubleCoset_finsum N r s c]
  rw [finsum_curry _ (compactPoincareDoubleCoset_hasFiniteSupport N r s c ψ φ),
    finsum_eq_sum_of_fintype]
  rfl

theorem gamma0CuspReducedMatrix_card_le (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Fintype.card (gamma0CuspReducedMatrix N r s c) ≤ (N * c) ^ 2 := by
  have h := Fintype.card_le_of_injective _ (gamma0CuspReducedMatrix_diagonal_injective N r s c)
  simpa only [Fintype.card_prod, ZMod.card, pow_two] using h

end ArtinMatthews
