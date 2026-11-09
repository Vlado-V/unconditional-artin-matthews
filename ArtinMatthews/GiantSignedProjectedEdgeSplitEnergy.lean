module

public import ArtinMatthews.GiantSignedStateEnergyTriangle
public import ArtinMatthews.GiantSignedProjectedLinear


set_option backward.privateInPublic true
@[expose] public section

/-! The actual projected raw family splits into its original clean and
dirty terms. The energy coefficient is the square of the sum of the
two norm coefficients. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedProjectedRawEdgeFamilyApply_split_energy
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    (R : ℕ) (patterns : Finset I) (C : I → B → Finset (Fin k))
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hclean : giantSignedStateEnergy PS ν
      (giantSignedProjectedRawEdgeFamilyApply R ν V patterns C κ q ρ θ ζ K
        (fun i s r => η i s r * giantSignedRawEdgeCleanMultiplier s r) f) ≤
        ENNReal.ofReal (A ^ 2) * giantSignedStateEnergy PS ν f)
    (hdirty : giantSignedStateEnergy PS ν
      (giantSignedProjectedRawEdgeFamilyApply R ν V patterns C κ q ρ θ ζ K
        (fun i s r => η i s r * giantSignedRawEdgeDirtyMultiplier s r) f) ≤
        ENNReal.ofReal (D ^ 2) * giantSignedStateEnergy PS ν f) :
    giantSignedStateEnergy PS ν
      (giantSignedProjectedRawEdgeFamilyApply R ν V patterns C κ q ρ θ ζ K η f) ≤
        ENNReal.ofReal ((A+D) ^ 2) * giantSignedStateEnergy PS ν f := by
  rw [giantSignedProjectedRawEdgeFamilyApply_clean_add_dirty]
  exact giantSignedStateEnergy_add_bound PS hVS ν hν f _ _ hA hD hclean hdirty

end
end ArtinMatthews
