module

public import ArtinMatthews.GiantSignedCopiedTarget
public import ArtinMatthews.GiantSignedEdgeEmpty
public import ArtinMatthews.GiantSignedTotalStepClean


set_option backward.privateInPublic true
@[expose] public section

/-! The actual empty store/promote term, with the original copied
coordinates, auxiliary law, total product and signed translation. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}

theorem giantSignedEdgeFixedApply_empty_copied {k ell : ℕ}
    (freshLaw : ∀ j, PB j → ℝ) (V : B → ℝ) (ρ : ℝ) (Δ : ℤ) (D : ℕ)
    (C : B → Finset (Fin k)) (a : MarkedPhysicalMarking PB (k+ell))
    (f : MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ)
    (m : GiantSignedMemory PB) :
    giantSignedEdgeFixedApply (fun j p => (freshLaw j p : ℂ)) V ρ Δ D
      (giantSignedPatternFreeLabels C a) (fun t m' => f (giantSignedPatternFill C a t) m') m
      (fun _ => ∅) (fun _ => ∅) =
        (giantSignedPendingDamping ρ m : ℂ) *
        (giantSignedPendingDamping ρ (giantSignedMemoryTranslate Δ m) : ℂ) *
          ∑ b : MarkedPhysicalMarking PB (k+ell), if IdealCopied C a b then
            (idealFreshTargetMass freshLaw C b : ℂ) * f b (giantSignedMemoryTranslate Δ m)
          else 0 := by
  rw [giantSignedEdgeFixedApply_empty]
  exact congrArg (fun z : ℂ => (giantSignedPendingDamping ρ m : ℂ) *
    (giantSignedPendingDamping ρ (giantSignedMemoryTranslate Δ m) : ℂ) * z)
    (giantSignedCopiedTarget_sum freshLaw C a (fun b => f b (giantSignedMemoryTranslate Δ m)))

/-- One literal store/promote term of a copied/fresh source pattern. -/
def giantSignedPatternEdgeTerm {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, PB j → ℝ) (V : B → ℝ)
    (C : B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell) (d : ℕ) (κ : ℤ)
    (stores promotions : (j : B) → Finset (Fin (ell + (C j).card)))
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k+ell) →
      GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k+ell))
    (m : GiantSignedMemory PB) : ℂ :=
  ∑ aux : GiantTwoSidedPatternAuxiliary PB C,
    let D := d * (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux)
    (idealAuxiliaryMass auxLaw aux : ℂ) * (D : ℂ) ^ ((ζ : ℂ) * Complex.I) *
      idealAdditivePhase θ D *
        giantSignedEdgeFixedApply (fun j p => (freshLaw j p : ℂ)) V ρ (κ * (D : ℤ)) D
          (giantSignedPatternFreeLabels C a)
          (fun t m' => K a (giantSignedPatternFill C a t) aux *
            f (giantTwoSidedResidueTranslate (κ * (D : ℤ)) y) (giantSignedPatternFill C a t) m')
          m stores promotions

theorem giantSignedPatternEdgeTerm_empty {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, PB j → ℝ) (V : B → ℝ)
    (C : B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell) (d : ℕ) (κ : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k+ell) →
      GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k+ell))
    (m : GiantSignedMemory PB) :
    giantSignedPatternEdgeTerm PS freshLaw auxLaw V C θ ζ ρ K d κ
      (fun _ => ∅) (fun _ => ∅) f y a m =
        (giantSignedPendingDamping ρ m : ℂ) *
          giantSignedTotalStepCleanPattern PS freshLaw auxLaw C θ ζ K d κ
            (fun y' b m' => (giantSignedPendingDamping ρ m' : ℂ) * f y' b m') y a m := by
  unfold giantSignedPatternEdgeTerm giantSignedTotalStepCleanPattern
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro aux _
  dsimp only
  let D := d * (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux)
  have he := giantSignedEdgeFixedApply_empty_copied freshLaw V ρ (κ * (D : ℤ)) D C a
    (fun b m' => K a b aux * f (giantTwoSidedResidueTranslate (κ * (D : ℤ)) y) b m') m
  rw [he]
  dsimp only [D]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : IdealCopied C a b
  · simp only [h, ite_true]
    ring
  · simp only [h, ite_false, mul_zero]

/-- Both big-label endpoint slot averages around the empty store/promote terms. -/
def giantSignedEdgeCleanApply {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, PB j → ℝ) (V : B → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) (d : ℕ) (κ : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k+ell) →
      GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k+ell))
    (m : GiantSignedMemory PB) : ℂ :=
  idealSlotAverage (fun b => ∑ i ∈ patterns,
    giantSignedPatternEdgeTerm PS freshLaw auxLaw V (C i) θ ζ ρ (K i) d κ
      (fun _ => ∅) (fun _ => ∅)
      (fun y' b' m' => idealSlotAverage (fun a' => f y' a' m') b') y b m) a

theorem giantSignedEdgeCleanApply_eq_totalStep {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, PB j → ℝ) (V : B → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) (d : ℕ) (κ : ℤ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k+ell) →
      GiantSignedMemory PB → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k+ell))
    (m : GiantSignedMemory PB) :
    giantSignedEdgeCleanApply PS freshLaw auxLaw V patterns C θ ζ ρ K d κ f y a m =
      giantSignedTotalStepCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K d κ f y a m := by
  have htest : (fun y' b' m' => (giantSignedPendingDamping ρ m' : ℂ) *
      idealSlotAverage (fun a' => f y' a' m') b') =
      (fun y' b' m' => idealSlotAverage
        (fun a' => (giantSignedPendingDamping ρ m' : ℂ) * f y' a' m') b') := by
    funext y' b' m'
    exact (giantSignedActiveMultiplier_slotAverage _ _ _).symm
  unfold giantSignedEdgeCleanApply giantSignedTotalStepCleanApply
  simp_rw [giantSignedPatternEdgeTerm_empty, htest]
  simp only [← Finset.mul_sum]
  rw [giantSignedActiveMultiplier_slotAverage]

end
end ArtinMatthews
