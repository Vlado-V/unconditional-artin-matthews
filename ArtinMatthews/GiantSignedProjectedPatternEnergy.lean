module

public import ArtinMatthews.GiantSignedProjectedLinear
public import ArtinMatthews.GiantSignedStateFiniteSumEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! A bound for every projected original pattern lifts to the literal
finite family under its common coefficient budget. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedProjectedRawEdgeFamilyApply_energy_of_patterns
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    (R : ℕ) (patterns : Finset I) (C : I → B → Finset (Fin k))
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (A : ℝ≥0∞)
    (hpattern : ∀ i ∈ patterns, giantSignedStateEnergy PS ν
      (giantSignedStateMemoryCutoff R
        (giantSignedRawEdgeApply ν V κ q ρ θ ζ (K i) (η i)
          (giantSignedStateMemoryCutoff R f))) ≤ A * giantSignedStateEnergy PS ν f) :
    giantSignedStateEnergy PS ν
      (giantSignedProjectedRawEdgeFamilyApply R ν V patterns C κ q ρ θ ζ K η f) ≤
      (patterns.card : ℝ≥0∞)^2 * A * giantSignedStateEnergy PS ν f := by
  classical
  let G (i : I) := giantSignedRawEdgeApply ν V κ q ρ θ ζ (K i) (η i)
    (giantSignedStateMemoryCutoff R f)
  let F (i : ↥patterns) := giantSignedStateMemoryCutoff R (G i.val)
  have hsum : giantSignedProjectedRawEdgeFamilyApply R ν V patterns C κ q ρ θ ζ K η f =
      fun s => ∑ i : ↥patterns, F i s := by
    change giantSignedStateMemoryCutoff R (fun s => ∑ i ∈ patterns, G i s) = _
    rw [giantSignedStateMemoryCutoff_finset_sum]
    funext s
    exact (Finset.sum_coe_sort patterns (fun i => giantSignedStateMemoryCutoff R (G i) s)).symm
  rw [hsum]
  have he := giantSignedStateEnergy_sum_le_card_sq PS hVS ν hν F
    (A * giantSignedStateEnergy PS ν f) (fun i => hpattern i.val i.property)
  simpa only [Fintype.card_coe, mul_assoc] using he

end
end ArtinMatthews
