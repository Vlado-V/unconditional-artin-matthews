module

public import ArtinMatthews.GiantSmallCanonicalPairing


set_option backward.privateInPublic true
@[expose] public section

/-! A prefix-dependent target parameter, such as the translated
pending memory, is fixed on the actual zero-extended tail fiber. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}

theorem giantSmallConditioningMap_prefix_target (q : ℝ)
    (d : MarkedPhysicalMarking P k)
    (w : MarkedPhysicalMarking P k → GiantTwoSidedResidueState P (k+ell) → ℂ)
    (y : GiantTwoSidedFullResidue P) :
    giantSmallConditioningMap P k ell q d (fun t => w (giantSmallPrefix t.val.2) t) y =
      giantSmallConditioningMap P k ell q d (w d) y := by
  unfold giantSmallConditioningMap
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  unfold giantSmallStateValue
  by_cases h : GiantSmallStateCondition y (giantSmallAppend d r)
  · simp only [dite_eq_left h, giantSmallPrefix_append]
  · simp only [dite_eq_right h]

variable [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val]

theorem giantSmallCanonicalPairing_eq_prefix_conditioned
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (q : ℝ)
    (w₁ : GiantTwoSidedResidueState P (k+ell) → ℂ)
    (w₂ : MarkedPhysicalMarking P k → GiantTwoSidedResidueState P (k+ell) → ℂ)
    (H : MarkedPhysicalMarking P k → GiantTwoSidedFullResidue P →
      GiantTwoSidedFullResidue P → ℂ) :
    giantSmallCanonicalPairing q w₁ (fun t => w₂ (giantSmallPrefix t.val.2) t) H =
      ∑ d : MarkedPhysicalMarking P k, ∑ y : GiantTwoSidedFullResidue P,
        ∑ y' : GiantTwoSidedFullResidue P,
          ((Fintype.card (GiantTwoSidedFullResidue P) : ℝ)⁻¹ : ℂ) *
            star (giantSmallConditioningMap P k ell q d w₁ y) * H d y y' *
              giantSmallConditioningMap P k ell q d (w₂ d) y' := by
  rw [giantSmallCanonicalPairing_eq_conditioned hV]
  simp_rw [giantSmallConditioningMap_prefix_target]

end
end ArtinMatthews
