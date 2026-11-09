module

public import ArtinMatthews.GiantSignedEdgeMoveExpansion
public import ArtinMatthews.GiantTwoSidedResiduePathExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! The unconditioned full-state signed edge. Small groups retain their
actual distinct zero lists. Big labels and all finite pending degrees
retain the literal store/promote choices of the source row. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] {PS : S → Finset ℕ} {PB : B → Finset ℕ}
    {k ell : ℕ}

structure GiantSignedRawEdgeMove (PS : S → Finset ℕ) (PB : B → Finset ℕ)
    {k : ℕ} (ell : ℕ) (C : B → Finset (Fin k)) (m : GiantSignedMemory PB) where
  sourceSmallPermutation : S → Equiv.Perm (Fin (k+ell))
  sourceBigPermutation : B → Equiv.Perm (Fin (k+ell))
  targetSmallPermutation : S → Equiv.Perm (Fin (k+ell))
  targetBigPermutation : B → Equiv.Perm (Fin (k+ell))
  auxiliary : GiantTwoSidedPatternAuxiliary PB C
  choice : GiantSignedEdgeChoice (fun g => ell + (C g).card) m.1
  smallTarget : GiantTwoSidedResidueState PS (k+ell)
  bigTarget : MarkedPhysicalMarking PB (k+ell)

instance [Fintype B] [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    {C : B → Finset (Fin k)} {m : GiantSignedMemory PB} :
    Fintype (GiantSignedRawEdgeMove PS PB ell C m) := by
  classical
  let encode (r : GiantSignedRawEdgeMove PS PB ell C m) :=
    ((r.sourceSmallPermutation, r.sourceBigPermutation),
      (r.targetSmallPermutation, r.targetBigPermutation),
      (r.auxiliary, r.choice), (r.smallTarget, r.bigTarget))
  apply Fintype.ofInjective encode
  intro a b h
  cases a
  cases b
  simp only [encode, Prod.mk.injEq] at h
  rcases h with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
  rfl

variable [Fintype B] [DecidableEq B] [DecidableEq S]
    {C : B → Finset (Fin k)}

def giantSignedRawEdgeSmallSource (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    GiantTwoSidedResidueState PS (k+ell) :=
  giantTwoSidedResiduePermute r.sourceSmallPermutation s.1

def giantSignedRawEdgeBigSource (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : MarkedPhysicalMarking PB (k+ell) :=
  giantSignedGroupedTuplePermutation r.sourceBigPermutation s.2.1

def giantSignedRawEdgeProduct (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : ℕ :=
  (∏ g : S, ∏ i : Fin k, ((giantSignedRawEdgeSmallSource s r).val.2 g (Fin.castAdd ell i)).val) *
    (giantTwoSidedPatternCopiedProduct C (giantSignedRawEdgeBigSource s r) *
      giantTwoSidedPatternAuxiliaryProduct r.auxiliary)

def giantSignedRawEdgeTarget (κ : ℤ) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : GiantSignedState PS PB (k+ell) :=
  ((giantTwoSidedResiduePermute r.targetSmallPermutation).symm r.smallTarget,
    (giantSignedGroupedTuplePermutation r.targetBigPermutation).symm r.bigTarget,
    giantSignedEdgeTarget (κ * (giantSignedRawEdgeProduct s r : ℤ)) s.2.2
      (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r)) r.choice)

def GiantSignedRawEdgeCondition (κ : ℤ) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : Prop :=
  (∀ g : S, ∀ i : Fin k, r.smallTarget.val.2 g (Fin.castAdd ell i) =
    (giantSignedRawEdgeSmallSource s r).val.2 g (Fin.castAdd ell i)) ∧
  r.smallTarget.val.1 =
    giantTwoSidedResidueTranslate (κ * (giantSignedRawEdgeProduct s r : ℤ))
      (giantSignedRawEdgeSmallSource s r).val.1 ∧
  IdealCopied C (giantSignedRawEdgeBigSource s r) r.bigTarget ∧
  (∀ g, ∀ i : Fin (r.choice.1 g).card,
    ¬ (giantSignedEdgeSelected (r.choice.1 g)
      (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r) g) i).val ∣
        giantSignedRawEdgeProduct s r) ∧
  (∀ g (a : ↥(C g)),
    (∀ j : S, ∀ i : Fin (k+ell),
      (r.auxiliary g a).val ≠ ((giantSignedRawEdgeSmallSource s r).val.2 j i).val ∧
      (r.auxiliary g a).val ≠ (r.smallTarget.val.2 j i).val) ∧
    (∀ j : B, ∀ i : Fin (k+ell),
      (r.auxiliary g a).val ≠ (giantSignedRawEdgeBigSource s r j i).val ∧
      (r.auxiliary g a).val ≠ (r.bigTarget j i).val))

def giantSignedRawEdgeCoefficient (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : ℂ :=
  if GiantSignedRawEdgeCondition κ s r then
    (giantTwoSidedResidueSlotNormalization (J := S) (k+ell) : ℂ) *
      (giantTwoSidedResidueSlotNormalization (J := B) (k+ell) : ℂ) *
      (∏ g : S, ((bandReciprocalMass (PS g))⁻¹ : ℂ)^ell) *
      (giantTwoSidedPatternAuxiliaryMass r.auxiliary : ℂ) *
      K (giantSignedRawEdgeBigSource s r) r.bigTarget r.auxiliary *
      (giantSignedRawEdgeProduct s r : ℂ)^((ζ : ℂ)*Complex.I) *
      idealAdditivePhase (θ * (κ : ℝ)) (giantSignedRawEdgeProduct s r) *
      (giantTwoSidedResidueDamping PS (k+ell) q (giantSignedRawEdgeSmallSource s r).val.1 : ℂ) *
      (giantTwoSidedResidueDamping PS (k+ell) q r.smallTarget.val.1 : ℂ) *
      giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ
        (κ * (giantSignedRawEdgeProduct s r : ℤ)) (giantSignedRawEdgeProduct s r)
        (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r))
        (giantSignedPatternFreeLabels C r.bigTarget) s.2.2 r.choice
  else 0

variable [Fintype (GiantTwoSidedResidueState PS (k+ell))]

def giantSignedRawEdgeApply (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (η : (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) : ℂ :=
  ∑ r : GiantSignedRawEdgeMove PS PB ell C s.2.2,
    giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r * η s r *
      f (giantSignedRawEdgeTarget κ s r)

theorem giantSignedRawEdgeApply_norm_le (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (η : (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (hη : ∀ s r, ‖η s r‖ ≤ 1) (f : GiantSignedState PS PB (k+ell) → ℂ)
    (s : GiantSignedState PS PB (k+ell)) :
    ‖giantSignedRawEdgeApply ν V κ q ρ θ ζ K η f s‖ ≤
      ∑ r : GiantSignedRawEdgeMove PS PB ell C s.2.2,
        ‖giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r‖ *
          ‖f (giantSignedRawEdgeTarget κ s r)‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r _
  rw [norm_mul, norm_mul]
  have hc : ‖giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r‖ * ‖η s r‖ ≤
      ‖giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r‖ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hη s r)
      (norm_nonneg (giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r))
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

def giantSignedRawEdgeFamilyApply {I : Type*} (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) : ℂ :=
  ∑ i ∈ patterns, giantSignedRawEdgeApply ν V κ q ρ θ ζ (K i) (η i) f s

end
end ArtinMatthews
