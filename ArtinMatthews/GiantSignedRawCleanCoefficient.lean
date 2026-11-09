module

public import ArtinMatthews.GiantSignedRawCleanMoveWeight
public import ArtinMatthews.GiantSignedRawCleanCondition
public import ArtinMatthews.GiantSmallCanonicalPairing
public import ArtinMatthews.GiantSignedCleanSector


set_option backward.privateInPublic true
@[expose] public section

/-! The actual empty-transfer coefficient has its canonical small
copied-prefix kernel, big fresh law and unchanged spectral phase. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {k ell : ℕ}
    {C : B → Finset (Fin k)}

def giantSignedCanonicalCleanProduct
    (d : MarkedPhysicalMarking PS k) (a : MarkedPhysicalMarking PB (k+ell))
    (aux : GiantTwoSidedPatternAuxiliary PB C) : ℕ :=
  markedPhysicalMarkingProduct d *
    (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux)

def GiantSignedCanonicalCleanSupport (κ : ℤ)
    (s t : GiantTwoSidedResidueState PS (k+ell))
    (a b : MarkedPhysicalMarking PB (k+ell)) (aux : GiantTwoSidedPatternAuxiliary PB C) : Prop :=
  giantSmallPrefix t.val.2 = giantSmallPrefix s.val.2 ∧
    t.val.1 = giantTwoSidedResidueTranslate
      (κ * (giantSignedCanonicalCleanProduct PS (giantSmallPrefix s.val.2) a aux : ℤ)) s.val.1 ∧
    IdealCopied C a b

def giantSignedCanonicalCleanCoefficient (ν : ∀ g, PB g → ℝ)
    (κ : ℤ) (q ρ Θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (s t : GiantTwoSidedResidueState PS (k+ell))
    (a b : MarkedPhysicalMarking PB (k+ell)) (aux : GiantTwoSidedPatternAuxiliary PB C)
    (m : GiantSignedMemory PB) : ℂ :=
  let D := giantSignedCanonicalCleanProduct PS (giantSmallPrefix s.val.2) a aux
  if GiantSignedCanonicalCleanSupport PS κ s t a b aux then
    (giantSmallTailMass PS ell : ℂ) *
      (idealAuxiliaryMass (fun g => markedHarmonicAtom (PB g)) aux : ℂ) *
      (if GiantSignedAuxiliaryBan C a b aux then K a b aux else 0) *
      (D : ℂ)^((ζ : ℂ)*Complex.I) * idealAdditivePhase Θ D *
      (giantTwoSidedResidueDamping PS (k+ell) q s.val.1 : ℂ) *
      (giantTwoSidedResidueDamping PS (k+ell) q t.val.1 : ℂ) *
      (idealFreshTargetMass ν C b : ℂ) * (giantSignedPendingDamping ρ m : ℂ) *
      (giantSignedPendingDamping ρ (giantSignedMemoryTranslate (κ * (D : ℤ)) m) : ℂ)
  else 0

omit [DecidableEq S] [DecidableEq B] in
theorem giantSignedRawClean_product
    (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    giantSignedRawEdgeProduct s r = giantSignedCanonicalCleanProduct PS
      (giantSmallPrefix (giantSignedRawEdgeSmallSource s r).val.2)
      (giantSignedRawEdgeBigSource s r) r.auxiliary := rfl

theorem giantSignedRawClean_coefficient_eq
    (hcross : ∀ g j, Disjoint (PB g) (PS j))
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) (hr : GiantSignedRawEdgeClean r) :
    giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r =
      (giantTwoSidedResidueSlotNormalization (J := S) (k+ell) : ℂ) *
      (giantTwoSidedResidueSlotNormalization (J := B) (k+ell) : ℂ) *
      giantSignedCanonicalCleanCoefficient PS ν κ q ρ (θ * (κ : ℝ)) ζ K
        (giantSignedRawEdgeSmallSource s r) r.smallTarget
        (giantSignedRawEdgeBigSource s r) r.bigTarget r.auxiliary s.2.2 := by
  have hpref :
      (∀ g : S, ∀ i : Fin k, r.smallTarget.val.2 g (Fin.castAdd ell i) =
        (giantSignedRawEdgeSmallSource s r).val.2 g (Fin.castAdd ell i)) ↔
      giantSmallPrefix r.smallTarget.val.2 =
        giantSmallPrefix (giantSignedRawEdgeSmallSource s r).val.2 := by
    constructor
    · intro h
      funext g i
      exact h g i
    · intro h g i
      exact congrFun (congrFun h g) i
  have hcond : GiantSignedRawEdgeCondition κ s r ↔
      GiantSignedCanonicalCleanSupport PS κ (giantSignedRawEdgeSmallSource s r) r.smallTarget
        (giantSignedRawEdgeBigSource s r) r.bigTarget r.auxiliary ∧
      GiantSignedAuxiliaryBan C (giantSignedRawEdgeBigSource s r) r.bigTarget r.auxiliary := by
    rw [giantSignedRawClean_condition_iff hcross κ s r hr, hpref]
    unfold GiantSignedCanonicalCleanSupport
    rw [giantSignedRawClean_product PS]
    tauto
  have htail : (∏ g : S, ((bandReciprocalMass (PS g))⁻¹ : ℂ)^ell) =
      (giantSmallTailMass PS ell : ℂ) := by
    simp only [giantSmallTailMass, Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_inv]
  have haux : giantTwoSidedPatternAuxiliaryMass r.auxiliary =
      idealAuxiliaryMass (fun g => markedHarmonicAtom (PB g)) r.auxiliary := rfl
  unfold giantSignedRawEdgeCoefficient giantSignedCanonicalCleanCoefficient
  rw [propext hcond, giantSignedRawClean_move_weight ν V κ ρ s r hr, htail, haux]
  rw [giantSignedRawClean_product PS]
  by_cases hs : GiantSignedCanonicalCleanSupport PS κ (giantSignedRawEdgeSmallSource s r)
      r.smallTarget (giantSignedRawEdgeBigSource s r) r.bigTarget r.auxiliary
  · by_cases hb : GiantSignedAuxiliaryBan C (giantSignedRawEdgeBigSource s r) r.bigTarget r.auxiliary
    · simp [hs, hb] <;> ring
    · simp [hs, hb]
  · simp [hs]

end
end ArtinMatthews
