module

public import ArtinMatthews.GiantTwoSidedPhysicalResidualExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! Residual patterns may be indexed by the big groups while the physical
states retain both small and big groups. The expansion keeps this distinction. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {B J : Type*} [DecidableEq B] [Fintype J] [DecidableEq J]
  {P : J → Finset ℕ} {k ell : ℕ} {Z : Finset ℕ}

theorem giantTwoSidedPhysicalCutoffPairing_mapped_residual_expansion
    (probes₁ probes₂ : Finset (B × Fin k))
    (C : IdealResidualPattern B k → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (Ψ : ℝ → ℂ) (x : ℝ) (f : ℕ → ℂ)
    (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) :
    giantTwoSidedPhysicalCutoffPairing (idealResidualPatterns probes₁ probes₂)
      C step q ζ K Ψ x f g =
      giantTwoSidedPhysicalPatternCutoffPairing (C none) step q ζ (K none) Ψ x f g +
      ∑ A ∈ probes₁.powerset.erase ∅, ∑ B' ∈ probes₂.powerset.erase ∅,
        giantTwoSidedPhysicalPatternCutoffPairing (C (some (A,B'))) step q ζ
          (K (some (A,B'))) Ψ x f g := by
  rw [giantTwoSidedPhysicalCutoffPairing_sum_patterns]
  have hd : Disjoint ({none} : Finset (IdealResidualPattern B k))
      ((probes₁.powerset.erase ∅ ×ˢ probes₂.powerset.erase ∅).image some) := by
    apply disjoint_singleton_left.mpr
    simp
  unfold idealResidualPatterns
  rw [sum_union hd, sum_singleton, sum_image]
  · rw [sum_product]
  · intro a _ b _ hab
    exact Option.some.inj hab

theorem giantTwoSidedPhysicalMappedRawCutoffPairing_norm_le
    (probes₁ probes₂ : Finset (B × Fin k))
    (C : IdealResidualPattern B k → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (Ψ : ℝ → ℂ) (x : ℝ) (f : ℕ → ℂ)
    (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) :
    ‖giantTwoSidedPhysicalPatternCutoffPairing (C none) step q ζ (K none) Ψ x f g‖ ≤
      ‖giantTwoSidedPhysicalCutoffPairing (idealResidualPatterns probes₁ probes₂)
        C step q ζ K Ψ x f g‖ +
      ∑ A ∈ probes₁.powerset.erase ∅, ∑ B' ∈ probes₂.powerset.erase ∅,
        ‖giantTwoSidedPhysicalPatternCutoffPairing (C (some (A,B'))) step q ζ
          (K (some (A,B'))) Ψ x f g‖ := by
  let comparisons := ∑ A ∈ probes₁.powerset.erase ∅, ∑ B' ∈ probes₂.powerset.erase ∅,
    giantTwoSidedPhysicalPatternCutoffPairing (C (some (A,B'))) step q ζ
      (K (some (A,B'))) Ψ x f g
  have hexp := giantTwoSidedPhysicalCutoffPairing_mapped_residual_expansion
    probes₁ probes₂ C step q ζ K Ψ x f g
  have hsum : ‖comparisons‖ ≤
      ∑ A ∈ probes₁.powerset.erase ∅, ∑ B' ∈ probes₂.powerset.erase ∅,
        ‖giantTwoSidedPhysicalPatternCutoffPairing (C (some (A,B'))) step q ζ
          (K (some (A,B'))) Ψ x f g‖ := by
    apply (norm_sum_le _ _).trans
    exact sum_le_sum (fun A _ => norm_sum_le _ _)
  calc
    _ = ‖giantTwoSidedPhysicalCutoffPairing (idealResidualPatterns probes₁ probes₂)
        C step q ζ K Ψ x f g - comparisons‖ := by
      rw [hexp]
      simp only [comparisons, add_sub_cancel_right]
    _ ≤ ‖giantTwoSidedPhysicalCutoffPairing (idealResidualPatterns probes₁ probes₂)
        C step q ζ K Ψ x f g‖ + ‖comparisons‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add le_rfl hsum

end
end ArtinMatthews
