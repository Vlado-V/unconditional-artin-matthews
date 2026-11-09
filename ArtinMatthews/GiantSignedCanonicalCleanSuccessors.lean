module

public import ArtinMatthews.GiantSignedRawCleanCoefficient
public import ArtinMatthews.GiantSmallConditioningPrefixTarget
public import ArtinMatthews.GiantSignedRawSlotAverage
public import ArtinMatthews.GiantSignedPatternEdgeDecomposition
public import ArtinMatthews.GiantSignedFullCleanForm
public import ArtinMatthews.GiantSignedPatternEdgeClean
public import ArtinMatthews.GiantSignedStateSlotPairing
public import ArtinMatthews.GiantSignedActiveSlotPairing
public import ArtinMatthews.GiantSignedBannedTotalCleanPairing
public import ArtinMatthews.GiantSignedCappedStatePairing
public import ArtinMatthews.GiantSignedProjectedWord
public import ArtinMatthews.IdealOriginalResidualConstruction
public import ArtinMatthews.GiantSignedResidualBudget
public import ArtinMatthews.IdealOriginalOperatorAdjoint


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical clean successor proofs assembled in dependency order. -/

-- Canonical successor of ArtinMatthews.GiantSignedRawCleanSmallPairing

/-! Conditioning the canonical clean small-state pair keeps the target
pending memory at the literal total-product translation for each prefix. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {k ell : ℕ}
    {C : B → Finset (Fin k)}

def giantSignedCanonicalCleanPrefixKernel (ν : ∀ g, PB g → ℝ)
    (κ : ℤ) (ρ Θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (a b : MarkedPhysicalMarking PB (k+ell))
    (aux : GiantTwoSidedPatternAuxiliary PB C) (m : GiantSignedMemory PB)
    (d : MarkedPhysicalMarking PS k) (y y' : GiantTwoSidedFullResidue PS) : ℂ :=
  let D := giantSignedCanonicalCleanProduct PS d a aux
  if y' = giantTwoSidedResidueTranslate (κ * (D : ℤ)) y ∧ IdealCopied C a b then
    (idealAuxiliaryMass (fun g => markedHarmonicAtom (PB g)) aux : ℂ) *
      (if GiantSignedAuxiliaryBan C a b aux then K a b aux else 0) *
      (D : ℂ)^((ζ : ℂ)*Complex.I) * idealAdditivePhase Θ D *
      (idealFreshTargetMass ν C b : ℂ) * (giantSignedPendingDamping ρ m : ℂ) *
      (giantSignedPendingDamping ρ (giantSignedMemoryTranslate (κ * (D : ℤ)) m) : ℂ)
  else 0

variable [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedCanonicalCleanSmall_pairing
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (κ : ℤ) (q ρ Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (a b : MarkedPhysicalMarking PB (k+ell))
    (aux : GiantTwoSidedPatternAuxiliary PB C) (m : GiantSignedMemory PB)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ) :
    (∑ s : GiantTwoSidedResidueState PS (k+ell),
      ∑ t : GiantTwoSidedResidueState PS (k+ell),
        (giantTwoSidedResidueHaarStateMass PS (k+ell) : ℂ) * star (w₁ (s,a,m)) *
          giantSignedCanonicalCleanCoefficient PS ν κ q ρ Θ ζ K s t a b aux m *
          w₂ (t,b,giantSignedMemoryTranslate
            (κ * (giantSignedCanonicalCleanProduct PS (giantSmallPrefix s.val.2) a aux : ℤ)) m)) =
      ∑ d : MarkedPhysicalMarking PS k, ∑ y : GiantTwoSidedFullResidue PS,
        ∑ y' : GiantTwoSidedFullResidue PS,
          (giantSignedSmallHaar PS : ℂ) * star (giantSignedSmallConditioning PS q d w₁ y a m) *
            giantSignedCanonicalCleanPrefixKernel PS ν κ ρ Θ ζ K a b aux m d y y' *
            giantSignedSmallConditioning PS q d w₂ y' b
              (giantSignedMemoryTranslate (κ * (giantSignedCanonicalCleanProduct PS d a aux : ℤ)) m) := by
  let W (d : MarkedPhysicalMarking PS k) (t : GiantTwoSidedResidueState PS (k+ell)) : ℂ :=
    w₂ (t,b,giantSignedMemoryTranslate (κ * (giantSignedCanonicalCleanProduct PS d a aux : ℤ)) m)
  let H := giantSignedCanonicalCleanPrefixKernel PS ν κ ρ Θ ζ K a b aux m
  have he := giantSmallCanonicalPairing_eq_prefix_conditioned hV q
    (fun s => w₁ (s,a,m)) W H
  have hh : ((Fintype.card (GiantTwoSidedFullResidue PS) : ℝ) : ℂ)⁻¹ =
      (giantSignedSmallHaar PS : ℂ) := by
    rw [← Complex.ofReal_inv, giantTwoSidedFullResidue_card]
    rfl
  rw [hh] at he
  refine Eq.trans ?_ he
  unfold giantSmallCanonicalPairing
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  by_cases hp : giantSmallPrefix t.val.2 = giantSmallPrefix s.val.2
  · by_cases hs : t.val.1 = giantTwoSidedResidueTranslate
        (κ * (giantSignedCanonicalCleanProduct PS (giantSmallPrefix s.val.2) a aux : ℤ)) s.val.1 ∧
        IdealCopied C a b
    · simp only [giantSignedCanonicalCleanCoefficient, GiantSignedCanonicalCleanSupport, H,
        giantSignedCanonicalCleanPrefixKernel, W, hp, hs, true_and, ite_true, Complex.ofReal_mul]
      ring
    · simp only [giantSignedCanonicalCleanCoefficient, GiantSignedCanonicalCleanSupport, H,
        giantSignedCanonicalCleanPrefixKernel, hp, hs, true_and, ite_true, ite_false,
        mul_zero, zero_mul]
  · simp only [giantSignedCanonicalCleanCoefficient, GiantSignedCanonicalCleanSupport,
      hp, false_and, ite_false, mul_zero, zero_mul]

end
end ArtinMatthews

-- Canonical successor of ArtinMatthews.GiantSignedRawCleanAverage

/-! The zero-store and zero-promotion part of the original finite row
has the canonical copied-prefix kernel between its two endpoint averages. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {k ell : ℕ}
    {C : B → Finset (Fin k)}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]

def giantSignedCanonicalCleanApply (ν : ∀ g, PB g → ℝ)
    (κ : ℤ) (q ρ Θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (s : GiantSignedState PS PB (k+ell)) : ℂ :=
  ∑ t : GiantTwoSidedPatternAuxiliary PB C ×
      (GiantTwoSidedResidueState PS (k+ell) × MarkedPhysicalMarking PB (k+ell)),
    giantSignedCanonicalCleanCoefficient PS ν κ q ρ Θ ζ K s.1 t.2.1 s.2.1 t.2.2 t.1 s.2.2 *
      f (t.2.1, t.2.2, giantSignedMemoryTranslate
        (κ * (giantSignedCanonicalCleanProduct PS (giantSmallPrefix s.1.val.2) s.2.1 t.1 : ℤ)) s.2.2)

theorem giantSignedCanonicalCleanApply_sum {I : Type*} [Fintype I]
    (ν : ∀ g, PB g → ℝ) (κ : ℤ) (q ρ Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell) (c : I → ℂ)
    (f : I → GiantSignedState PS PB (k+ell) → ℂ)
    (s : GiantSignedState PS PB (k+ell)) :
    giantSignedCanonicalCleanApply PS ν κ q ρ Θ ζ K (fun t => ∑ i, c i * f i t) s =
      ∑ i, c i * giantSignedCanonicalCleanApply PS ν κ q ρ Θ ζ K (f i) s := by
  unfold giantSignedCanonicalCleanApply
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem giantSignedRawCleanApply_eq_endpoint_sums
    (hcross : ∀ g j, Disjoint (PB g) (PS j))
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawCleanApply ν V κ q ρ θ ζ K f s =
      ∑ π : GiantSignedStateSlotPermutations S B (k+ell),
      ∑ τ : GiantSignedStateSlotPermutations S B (k+ell),
        (giantTwoSidedResidueSlotNormalization (J := S) (k+ell) : ℂ) *
          (giantTwoSidedResidueSlotNormalization (J := B) (k+ell) : ℂ) *
          giantSignedCanonicalCleanApply PS ν κ q ρ (θ * (κ : ℝ)) ζ K
            (fun t => f ((giantSignedStatePermute PS τ.1 τ.2).symm t))
            (giantSignedStatePermute PS π.1 π.2 s) := by
  rw [giantSignedRawCleanApply_expand]
  simp only [GiantSignedStateSlotPermutations, Fintype.sum_prod_type,
    giantSignedCanonicalCleanApply, Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro πS _
  apply Finset.sum_congr (by ext; simp)
  intro πB _
  apply Finset.sum_congr (by ext; simp)
  intro τS _
  apply Finset.sum_congr (by ext; simp)
  intro τB _
  apply Finset.sum_congr (by ext; simp)
  intro aux _
  apply Finset.sum_congr (by ext; simp)
  intro tS _
  apply Finset.sum_congr (by ext; simp)
  intro tB _
  let r : GiantSignedRawEdgeMove PS PB ell C s.2.2 :=
    ⟨πS, πB, τS, τB, aux, giantSignedEmptyEdgeChoice s.2.2, tS, tB⟩
  have hr : GiantSignedRawEdgeClean r := ⟨rfl, rfl⟩
  have ht : giantSignedRawEdgeTarget κ s r =
      (giantSignedStatePermute PS τS τB).symm
        (tS, tB, giantSignedMemoryTranslate (κ * (giantSignedRawEdgeProduct s r : ℤ)) s.2.2) := by
    exact Prod.ext rfl (Prod.ext rfl (giantSignedRawClean_target_memory κ s r hr))
  change giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r *
      f (giantSignedRawEdgeTarget κ s r) = _
  rw [giantSignedRawClean_coefficient_eq PS hcross ν V κ q ρ θ ζ K s r hr, ht,
    giantSignedRawClean_product PS]
  exact mul_assoc _ _ _

theorem giantSignedRawCleanApply_eq_slotAverage
    (hcross : ∀ g j, Disjoint (PB g) (PS j))
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawCleanApply ν V κ q ρ θ ζ K f s =
      giantSignedStateSlotAverage PS
        (giantSignedCanonicalCleanApply PS ν κ q ρ (θ * (κ : ℝ)) ζ K
          (giantSignedStateSlotAverage PS f)) s := by
  rw [giantSignedRawCleanApply_eq_endpoint_sums PS hcross]
  simp_rw [giantSignedRawSlotNormalization]
  let W : ℂ := (((Fintype.card (GiantSignedStateSlotPermutations S B (k+ell)) : ℝ)⁻¹ : ℝ) : ℂ)
  have hAverage : giantSignedStateSlotAverage PS f =
      fun t => ∑ τ : GiantSignedStateSlotPermutations S B (k+ell),
        W * f ((giantSignedStatePermute PS τ.1 τ.2).symm t) := by
    funext t
    exact (giantSignedStateSlotAverage_inverse PS f t).symm
  rw [hAverage]
  change (∑ π : GiantSignedStateSlotPermutations S B (k+ell),
      ∑ τ : GiantSignedStateSlotPermutations S B (k+ell), W^2 *
        giantSignedCanonicalCleanApply PS ν κ q ρ (θ * (κ : ℝ)) ζ K
          (fun t => f ((giantSignedStatePermute PS τ.1 τ.2).symm t))
          (giantSignedStatePermute PS π.1 π.2 s)) =
    ∑ π : GiantSignedStateSlotPermutations S B (k+ell), W *
      giantSignedCanonicalCleanApply PS ν κ q ρ (θ * (κ : ℝ)) ζ K
        (fun t => ∑ τ : GiantSignedStateSlotPermutations S B (k+ell),
          W * f ((giantSignedStatePermute PS τ.1 τ.2).symm t))
        (giantSignedStatePermute PS π.1 π.2 s)
  apply Finset.sum_congr rfl
  intro π _
  rw [giantSignedCanonicalCleanApply_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  ring

end
end ArtinMatthews

-- Canonical successor of ArtinMatthews.GiantSignedFullEdgeClean

/-! The full-memory conditioned pairing uses the actual empty
store/promote row at every ordered small prefix. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (j : B) (p : PB j), NeZero p.val]

def giantSignedFullEdgeCleanPairing {I : Type*} {k ell : ℕ}
    (ν freshLaw auxLaw : ∀ j, PB j → ℝ) (V : B → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ q : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) (κ : ℤ)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ) : ℂ :=
  giantSignedConditionedPairing PS ν (fun d => giantSignedSmallConditioning PS q d w₁)
    (fun d => giantSignedEdgeCleanApply PS freshLaw auxLaw V patterns C θ ζ ρ K
      (markedPhysicalMarkingProduct d) κ (giantSignedSmallConditioning PS q d w₂))

omit [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
  [∀ (j : B) (p : PB j), NeZero p.val] in
theorem giantSignedFullEdgeCleanPairing_eq_totalPairing {I : Type*} {k ell : ℕ}
    (ν freshLaw auxLaw : ∀ j, PB j → ℝ) (V : B → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ q : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) (κ : ℤ)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedFullEdgeCleanPairing PS ν freshLaw auxLaw V patterns C θ ζ ρ q K κ w₁ w₂ =
      giantSignedConditionedPairing PS ν (fun d => giantSignedSmallConditioning PS q d w₁)
        (fun d => giantSignedTotalStepCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K
          (markedPhysicalMarkingProduct d) κ (giantSignedSmallConditioning PS q d w₂)) := by
  have he (d : MarkedPhysicalMarking PS k) :
      giantSignedEdgeCleanApply PS freshLaw auxLaw V patterns C θ ζ ρ K
        (markedPhysicalMarkingProduct d) κ (giantSignedSmallConditioning PS q d w₂) =
      giantSignedTotalStepCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K
        (markedPhysicalMarkingProduct d) κ (giantSignedSmallConditioning PS q d w₂) := by
    funext y a m
    exact giantSignedEdgeCleanApply_eq_totalStep PS freshLaw auxLaw V patterns C θ ζ ρ K
      (markedPhysicalMarkingProduct d) κ _ y a m
  unfold giantSignedFullEdgeCleanPairing
  simp_rw [he]

theorem giantSignedFullEdgeCleanPairing_eq_form {I : Type*} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν freshLaw auxLaw : ∀ j, PB j → ℝ) (V : B → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ q : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) (κ : ℤ)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ)
    (hs : let F := fun d => giantSignedSmallConditioning PS q d w₁
      let G := fun d => giantSignedTotalStepCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K
        (markedPhysicalMarkingProduct d) κ (giantSignedSmallConditioning PS q d w₂)
      Summable (fun i : GiantSignedConditionedIndex PS (PB := PB) k ell =>
        (giantSignedConditionedWeight PS ν i : ℂ) *
          star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i)) :
    giantSignedFullEdgeCleanPairing PS ν freshLaw auxLaw V patterns C θ ζ ρ q K κ w₁ w₂ =
      giantSignedFullCleanForm PS ν freshLaw auxLaw patterns C θ ζ ρ q K κ w₁ w₂ := by
  rw [giantSignedFullEdgeCleanPairing_eq_totalPairing,
    giantSignedFullCleanForm_eq_pairing PS hV ν freshLaw auxLaw patterns C θ ζ ρ q K κ w₁ w₂ hs]

theorem giantSignedFullEdgeCleanPairing_energy {I : Type*} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (hP : ∀ j p, p ∈ PS j → p.Prime)
    (ν : ∀ j, PB j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (freshLaw auxLaw : ∀ j, PB j → ℝ) (V : B → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ q U L : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hL : 0 ≤ L)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) (κ : ℤ)
    (hIdeal : ∀ Θ (h : MarkedPhysicalMarking PB (k+ell) → ℂ), IdealSymmetric h →
      (∑ a, giantSignedActiveMass ν a *
        ‖idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ K h a‖ ^ 2) ≤
          U ^ 2 * ∑ a, giantSignedActiveMass ν a * ‖h a‖ ^ 2)
    (hSmall : ∀ f : GiantTwoSidedResidueState PS (k+ell) → ℂ,
      (∑ d : MarkedPhysicalMarking PS k,
        giantSmallResidueEnergy (giantSmallConditioningMap PS k ell q d f)) ≤
          L * giantSmallStateEnergy f)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ)
    (hw₁ : giantSignedStateEnergy PS ν w₁ ≠ ∞)
    (hw₂ : giantSignedStateEnergy PS ν w₂ ≠ ∞)
    (hsym : ∀ s m, IdealSymmetric (fun a => w₂ (s, a, m))) :
    ENNReal.ofReal (‖giantSignedFullEdgeCleanPairing PS ν freshLaw auxLaw V
      patterns C θ ζ ρ q K κ w₁ w₂‖ ^ 2) ≤
      ENNReal.ofReal (U ^ 2 * L ^ 2) *
        giantSignedStateEnergy PS ν w₁ * giantSignedStateEnergy PS ν w₂ := by
  rw [giantSignedFullEdgeCleanPairing_eq_totalPairing]
  exact (giantSignedTotalClean_pairing_bound PS hV ν hν freshLaw auxLaw patterns C ζ ρ U q L
    hρ hρ1 hL K (fun _ => θ) markedPhysicalMarkingProduct
    (giantSignedSmallPrefixProduct_pos hP) (fun _ => κ) hIdeal hSmall w₁ w₂ hw₁ hw₂ hsym).2

end
end ArtinMatthews

-- Canonical successor of ArtinMatthews.GiantSignedRawCleanPrefixApply

/-! The conditioned canonical kernel sums to the actual empty
store/promotion row with the same auxiliary law and full ban. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {k ell : ℕ}
    {C : B → Finset (Fin k)}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedCanonicalCleanPrefixKernel_apply
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (ρ Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (d : MarkedPhysicalMarking PS k) (y : GiantTwoSidedFullResidue PS)
    (a : MarkedPhysicalMarking PB (k+ell)) (m : GiantSignedMemory PB)
    (F : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k+ell) →
      GiantSignedMemory PB → ℂ) :
    (∑ aux : GiantTwoSidedPatternAuxiliary PB C, ∑ b : MarkedPhysicalMarking PB (k+ell),
      ∑ y' : GiantTwoSidedFullResidue PS,
        giantSignedCanonicalCleanPrefixKernel PS ν κ ρ Θ ζ K a b aux m d y y' *
          F y' b (giantSignedMemoryTranslate
            (κ * (giantSignedCanonicalCleanProduct PS d a aux : ℤ)) m)) =
      giantSignedPatternEdgeTerm PS ν (fun j => markedHarmonicAtom (PB j)) V C Θ ζ ρ
        (fun a b aux => if GiantSignedAuxiliaryBan C a b aux then K a b aux else 0)
        (markedPhysicalMarkingProduct d) κ (fun _ => ∅) (fun _ => ∅) F y a m := by
  rw [giantSignedPatternEdgeTerm_empty]
  unfold giantSignedTotalStepCleanPattern
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro aux _
  apply Finset.sum_congr rfl
  intro b _
  let y₀ := giantTwoSidedResidueTranslate
    (κ * (giantSignedCanonicalCleanProduct PS d a aux : ℤ)) y
  by_cases hab : IdealCopied C a b
  · rw [Finset.sum_eq_single y₀]
    · simp only [giantSignedCanonicalCleanPrefixKernel, giantSignedCanonicalCleanProduct,
        y₀, hab, eq_self, true_and, and_true, ite_true]
      ring
    · intro y' _ hy'
      have hne : y' ≠ giantTwoSidedResidueTranslate
          (κ * (giantSignedCanonicalCleanProduct PS d a aux : ℤ)) y := hy'
      simp only [giantSignedCanonicalCleanPrefixKernel, hne, false_and, ite_false, zero_mul]
    · intro hy
      exact (hy (Finset.mem_univ _)).elim
  · simp only [giantSignedCanonicalCleanPrefixKernel, hab, and_false, ite_false, zero_mul,
      mul_zero, Finset.sum_const_zero]

end
end ArtinMatthews

-- Canonical successor of ArtinMatthews.GiantSignedCanonicalCleanPairing

/-! The canonical original-state pairing conditions exactly on each
small copied prefix while leaving the pending prime-list measure intact. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {k ell : ℕ}
    {C : B → Finset (Fin k)}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedCanonicalCleanFiberPairing_eq_conditioned
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ) (m : GiantSignedMemory PB) :
    giantSignedStateFiberPairing PS ν w₁
      (giantSignedCanonicalCleanApply PS ν κ q ρ Θ ζ K w₂) m =
      ∑ d : MarkedPhysicalMarking PS k, ∑ y : GiantTwoSidedFullResidue PS,
        ∑ a : MarkedPhysicalMarking PB (k+ell),
          (giantSignedSmallHaar PS * giantSignedMemoryMass ν m * giantSignedActiveMass ν a : ℂ) *
            star (giantSignedSmallConditioning PS q d w₁ y a m) *
            giantSignedPatternEdgeTerm PS ν (fun j => markedHarmonicAtom (PB j)) V C Θ ζ ρ
              (fun a b aux => if GiantSignedAuxiliaryBan C a b aux then K a b aux else 0)
              (markedPhysicalMarkingProduct d) κ (fun _ => ∅) (fun _ => ∅)
              (giantSignedSmallConditioning PS q d w₂) y a m := by
  let X := GiantTwoSidedResidueState PS (k+ell)
  let A := MarkedPhysicalMarking PB (k+ell)
  let U := GiantTwoSidedPatternAuxiliary PB C
  let D := MarkedPhysicalMarking PS k
  let Y := GiantTwoSidedFullResidue PS
  let W (a : A) : ℂ := (giantSignedMemoryMass ν m * giantSignedActiveMass ν a : ℂ)
  let F (a : A) (aux : U) (b : A) (s t : X) : ℂ :=
    (giantTwoSidedResidueHaarStateMass PS (k+ell) : ℂ) * star (w₁ (s,a,m)) *
      giantSignedCanonicalCleanCoefficient PS ν κ q ρ Θ ζ K s t a b aux m *
      w₂ (t,b,giantSignedMemoryTranslate
        (κ * (giantSignedCanonicalCleanProduct PS (giantSmallPrefix s.val.2) a aux : ℤ)) m)
  let G (a : A) (aux : U) (b : A) (d : D) (y y' : Y) : ℂ :=
    (giantSignedSmallHaar PS : ℂ) * star (giantSignedSmallConditioning PS q d w₁ y a m) *
      giantSignedCanonicalCleanPrefixKernel PS ν κ ρ Θ ζ K a b aux m d y y' *
      giantSignedSmallConditioning PS q d w₂ y' b
        (giantSignedMemoryTranslate (κ * (giantSignedCanonicalCleanProduct PS d a aux : ℤ)) m)
  have hsmall (a : A) (aux : U) (b : A) : (∑ s : X, ∑ t : X, F a aux b s t) =
      ∑ d : D, ∑ y : Y, ∑ y' : Y, G a aux b d y y' :=
    giantSignedCanonicalCleanSmall_pairing PS hV ν κ q ρ Θ ζ K a b aux m w₁ w₂
  have hleft : giantSignedStateFiberPairing PS ν w₁
      (giantSignedCanonicalCleanApply PS ν κ q ρ Θ ζ K w₂) m =
      ∑ a : A, ∑ aux : U, ∑ b : A, W a * ∑ s : X, ∑ t : X, F a aux b s t := by
    unfold giantSignedStateFiberPairing giantSignedCanonicalCleanApply
    simp only [Fintype.sum_prod_type, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    calc
      _ = ∑ s : X, ∑ aux : U, ∑ t : X, ∑ b : A, W a * F a aux b s t := by
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro aux _
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro b _
        simp only [W, F, giantSignedStateMass, Complex.ofReal_mul]
        ring
      _ = ∑ aux : U, ∑ s : X, ∑ t : X, ∑ b : A, W a * F a aux b s t := Finset.sum_comm
      _ = ∑ aux : U, ∑ s : X, ∑ b : A, ∑ t : X, W a * F a aux b s t := by
        apply Finset.sum_congr rfl
        intro aux _
        apply Finset.sum_congr rfl
        intro s _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro aux _
        exact Finset.sum_comm
  rw [hleft]
  simp_rw [hsmall, Finset.mul_sum]
  calc
    _ = ∑ i : A × (U × A), ∑ j : D × Y, ∑ y' : Y,
        W i.1 * G i.1 i.2.1 i.2.2 j.1 j.2 y' := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ j : D × Y, ∑ i : A × (U × A), ∑ y' : Y,
        W i.1 * G i.1 i.2.1 i.2.2 j.1 j.2 y' := Finset.sum_comm
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro a _
      rw [← giantSignedCanonicalCleanPrefixKernel_apply PS ν V κ ρ Θ ζ K d y a m]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro aux _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro y' _
      simp only [W, G]
      ring

end
end ArtinMatthews

-- Canonical successor of ArtinMatthews.GiantSignedRawCleanFamilyBlock

/-! The original raw clean family has the exact conditioned pairing on
each full pending-memory fiber. The endpoint averages keep the original
small-state and active-label measures. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedRawCleanFamilyFiberPairing_eq_conditioned
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (hcross : ∀ g j, Disjoint (PB g) (PS j))
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ) (m : GiantSignedMemory PB) :
    giantSignedStateFiberPairing PS ν w₁
      (giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K
        (fun _ => giantSignedRawEdgeCleanMultiplier) w₂) m =
      ∑ d : MarkedPhysicalMarking PS k, ∑ y : GiantTwoSidedFullResidue PS,
        ∑ a : MarkedPhysicalMarking PB (k+ell),
          (giantSignedSmallHaar PS * giantSignedMemoryMass ν m * giantSignedActiveMass ν a : ℂ) *
            star (giantSignedSmallConditioning PS q d (giantSignedStateSlotAverage PS w₁) y a m) *
            giantSignedEdgeCleanApply PS ν (fun j => markedHarmonicAtom (PB j)) V patterns C
              (θ * (κ : ℝ)) ζ ρ
              (fun i a b aux => if GiantSignedAuxiliaryBan (C i) a b aux then K i a b aux else 0)
              (markedPhysicalMarkingProduct d) κ
              (giantSignedSmallConditioning PS q d (giantSignedStateSlotAverage PS w₂)) y a m := by
  let F := giantSignedStateSlotAverage PS w₁
  let G := giantSignedStateSlotAverage PS w₂
  let L (d : MarkedPhysicalMarking PS k) (y : GiantTwoSidedFullResidue PS)
      (a : MarkedPhysicalMarking PB (k+ell)) (i : I) : ℂ :=
    giantSignedPatternEdgeTerm PS ν (fun j => markedHarmonicAtom (PB j)) V (C i)
      (θ * (κ : ℝ)) ζ ρ
      (fun a b aux => if GiantSignedAuxiliaryBan (C i) a b aux then K i a b aux else 0)
      (markedPhysicalMarkingProduct d) κ (fun _ => ∅) (fun _ => ∅)
      (giantSignedSmallConditioning PS q d G) y a m
  let W (a : MarkedPhysicalMarking PB (k+ell)) : ℂ :=
    (giantSignedSmallHaar PS * giantSignedMemoryMass ν m * giantSignedActiveMass ν a : ℂ)
  have hterm (i : I) : giantSignedStateFiberPairing PS ν w₁
      (giantSignedRawEdgeApply ν V κ q ρ θ ζ (K i) giantSignedRawEdgeCleanMultiplier w₂) m =
      ∑ d : MarkedPhysicalMarking PS k, ∑ y : GiantTwoSidedFullResidue PS,
        ∑ a : MarkedPhysicalMarking PB (k+ell),
          W a * star (giantSignedSmallConditioning PS q d F y a m) * L d y a i := by
    have he : giantSignedRawEdgeApply ν V κ q ρ θ ζ (K i) giantSignedRawEdgeCleanMultiplier w₂ =
        giantSignedStateSlotAverage PS
          (giantSignedCanonicalCleanApply PS ν κ q ρ (θ * (κ : ℝ)) ζ (K i) G) := by
      funext s
      rw [← giantSignedRawCleanApply_eq_split]
      exact giantSignedRawCleanApply_eq_slotAverage PS hcross ν V κ q ρ θ ζ (K i) w₂ s
    rw [he, giantSignedStateFiberPairing_slotAverage]
    exact giantSignedCanonicalCleanFiberPairing_eq_conditioned PS hV ν V κ q ρ
      (θ * (κ : ℝ)) ζ (K i) F G m
  have hfamily : giantSignedStateFiberPairing PS ν w₁
      (giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K
        (fun _ => giantSignedRawEdgeCleanMultiplier) w₂) m =
      ∑ i ∈ patterns, giantSignedStateFiberPairing PS ν w₁
        (giantSignedRawEdgeApply ν V κ q ρ θ ζ (K i) giantSignedRawEdgeCleanMultiplier w₂) m := by
    unfold giantSignedStateFiberPairing giantSignedRawEdgeFamilyApply
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  have htarget (d : MarkedPhysicalMarking PS k) :
      (fun y b m' => idealSlotAverage
        (fun a' => giantSignedSmallConditioning PS q d G y a' m') b) =
        giantSignedSmallConditioning PS q d G := by
    funext y b m'
    exact congrFun (idealSlotAverage_fixed _ (giantSignedSmallConditioning_symmetric PS q d G
      (giantSignedStateSlotAverage_bigSymmetric PS w₂) y m')) b
  rw [hfamily]
  simp_rw [hterm]
  calc
    _ = ∑ d : MarkedPhysicalMarking PS k, ∑ y : GiantTwoSidedFullResidue PS,
        ∑ a : MarkedPhysicalMarking PB (k+ell), ∑ i ∈ patterns,
          W a * star (giantSignedSmallConditioning PS q d F y a m) * L d y a i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro y _
      unfold giantSignedEdgeCleanApply
      rw [htarget d]
      let c : ℂ := (giantSignedSmallHaar PS * giantSignedMemoryMass ν m : ℂ)
      let f (a : MarkedPhysicalMarking PB (k+ell)) := giantSignedSmallConditioning PS q d F y a m
      let g (a : MarkedPhysicalMarking PB (k+ell)) := ∑ i ∈ patterns, L d y a i
      have hf : IdealSymmetric f := giantSignedSmallConditioning_symmetric PS q d F
        (giantSignedStateSlotAverage_bigSymmetric PS w₁) y m
      calc
        _ = c * ∑ a, (giantSignedActiveMass ν a : ℂ) * star (f a) * g a := by
          simp only [g, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro i _
          simp only [W, c, f]
          ring
        _ = c * ∑ a, (giantSignedActiveMass ν a : ℂ) * star (f a) * idealSlotAverage g a :=
          congrArg (fun z : ℂ => c*z) (giantSignedActiveSlotPairing_fixed ν f g hf).symm
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          dsimp only [c, f, g, L, F, G]
          ring

end
end ArtinMatthews

-- Canonical successor of ArtinMatthews.GiantSignedRawCleanFamilyPairing

/-! The actual raw family pairing sums every pending memory. Its finite
fiber identities combine by absolute convergence of the conditioned form. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem tsum_memory_first {D M Y A : Type*} [Fintype D] [Fintype Y] [Fintype A]
    (f : D × (M × (Y × A)) → ℂ) (hs : Summable f) :
    (∑' i, f i) = ∑' m : M, ∑ d : D, ∑ y : Y, ∑ a : A, f (d,m,y,a) := by
  let e : M × (D × (Y × A)) ≃ D × (M × (Y × A)) :=
    { toFun := fun z => (z.2.1, (z.1, z.2.2))
      invFun := fun z => (z.2.1, (z.1, z.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he : Summable (fun z => f (e z)) := hs.comp_injective e.injective
  rw [← e.tsum_eq f, he.tsum_prod]
  simp only [tsum_fintype, Fintype.sum_prod_type, e, Equiv.coe_fn_mk]

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedConditionedPairing_memoryFibers
    (ν : ∀ g, PB g → ℝ)
    (F G : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ)
    (hs : Summable (fun i : GiantSignedConditionedIndex PS (PB := PB) k ell =>
      (giantSignedConditionedWeight PS ν i : ℂ) *
        star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i)) :
    giantSignedConditionedPairing PS ν F G =
      ∑' m : GiantSignedMemory PB, ∑ d : MarkedPhysicalMarking PS k,
        ∑ y : GiantTwoSidedFullResidue PS, ∑ a : MarkedPhysicalMarking PB (k+ell),
          (giantSignedSmallHaar PS * giantSignedMemoryMass ν m * giantSignedActiveMass ν a : ℂ) *
            star (F d y a m) * G d y a m := by
  refine (tsum_memory_first
    (D := MarkedPhysicalMarking PS k) (M := GiantSignedMemory PB)
    (Y := GiantTwoSidedFullResidue PS) (A := MarkedPhysicalMarking PB (k+ell))
    (fun i => (giantSignedConditionedWeight PS ν i : ℂ) *
      star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i) hs).trans ?_
  apply tsum_congr
  intro m
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  simp only [giantSignedConditionedWeight, giantSignedConditionedValue, Complex.ofReal_mul]

def giantSignedRawCleanFamilyPairing
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ) : ℂ :=
  ∑' m : GiantSignedMemory PB, giantSignedStateFiberPairing PS ν w₁
    (giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K
      (fun _ => giantSignedRawEdgeCleanMultiplier) w₂) m

theorem giantSignedRawCleanFamilyPairing_eq_conditioned
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (hcross : ∀ g j, Disjoint (PB g) (PS j))
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ)
    (hs : let F := fun d => giantSignedSmallConditioning PS q d (giantSignedStateSlotAverage PS w₁)
      let G := fun d => giantSignedEdgeCleanApply PS ν (fun j => markedHarmonicAtom (PB j)) V
        patterns C (θ * (κ : ℝ)) ζ ρ
        (fun i a b aux => if GiantSignedAuxiliaryBan (C i) a b aux then K i a b aux else 0)
        (markedPhysicalMarkingProduct d) κ
        (giantSignedSmallConditioning PS q d (giantSignedStateSlotAverage PS w₂))
      Summable (fun i : GiantSignedConditionedIndex PS (PB := PB) k ell =>
        (giantSignedConditionedWeight PS ν i : ℂ) *
          star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i)) :
    giantSignedRawCleanFamilyPairing PS ν V patterns C κ q ρ θ ζ K w₁ w₂ =
      giantSignedFullEdgeCleanPairing PS ν ν (fun j => markedHarmonicAtom (PB j)) V patterns C
        (θ * (κ : ℝ)) ζ ρ q
        (fun i a b aux => if GiantSignedAuxiliaryBan (C i) a b aux then K i a b aux else 0)
        κ (giantSignedStateSlotAverage PS w₁) (giantSignedStateSlotAverage PS w₂) := by
  unfold giantSignedFullEdgeCleanPairing giantSignedRawCleanFamilyPairing
  rw [giantSignedConditionedPairing_memoryFibers PS ν _ _ hs]
  exact tsum_congr (giantSignedRawCleanFamilyFiberPairing_eq_conditioned PS hV hcross
    ν V patterns C κ q ρ θ ζ K w₁ w₂)

end
end ArtinMatthews

-- Canonical successor of ArtinMatthews.GiantSignedBannedRawCleanFamilyPairing

/-! The original raw clean family pairing has the actual harmonic ideal
bound after the exact tilt, ban and small-prefix conditioning. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (j : B) (p : PB j), NeZero p.val]

theorem giantSignedBannedRawCleanFamilyPairing_energy {I : Type*} {k ell n : ℕ}
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hPS : ∀ j p, p ∈ PS j → p.Prime)
    (hcross : ∀ g j, Disjoint (PB g) (PS j))
    (hP : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PB i) (PB j)))
    (v Pmin : ℝ) (hv : 0 < v) (hPmin : 0 < Pmin)
    (hVB : ∀ j, v ≤ bandReciprocalMass (PB j)) (hp : ∀ j (p : PB j), Pmin ≤ p.val)
    (qStage : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ qStage i) (hq1 : ∀ i, qStage i ≤ 1)
    (hsmall : (n : ℝ) / Pmin < 1)
    (V : B → ℝ) (patterns : Finset I) (C : I → B → Finset (Fin k)) (θ ζ ρ : ℝ) (κ : ℤ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (cost : I → ℝ) (hcost : ∀ i ∈ patterns, 0 ≤ cost i)
    (hK : ∀ i ∈ patterns, ∀ a b aux, ‖K i a b aux‖ ≤ cost i)
    (freshCount comparisonCount : ℕ)
    (hFreshCount : ∀ i ∈ patterns, (∑ j, ((C i j).card + ell)) ≤ freshCount)
    (hComparisonCount : ∀ i ∈ patterns, (∑ j, (C i j).card) * (2 * (k+ell)) ≤ comparisonCount)
    (hDensitySmall : (freshCount : ℝ) * ((n : ℝ) / Pmin) ≤ 1 / 2)
    (U : ℝ) (hU : 0 ≤ U)
    (hOriginal : ∀ Θ (f : MarkedPhysicalMarking PB (k+ell) → ℂ), IdealSymmetric f →
      idealLabelEnergy PB (k+ell) (idealOperator patterns C Θ ζ K f) ≤
        U ^ 2 * idealLabelEnergy PB (k+ell) f)
    (qSmall L : ℝ) (hL : 0 ≤ L)
    (hSmall : ∀ f : GiantTwoSidedResidueState PS (k+ell) → ℂ,
      (∑ d : MarkedPhysicalMarking PS k,
        giantSmallResidueEnergy (giantSmallConditioningMap PS k ell qSmall d f)) ≤
          L * giantSmallStateEnergy f)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ)
    (hw₁ : giantSignedStateEnergy PS (fun j => giantSignedTiltedPrimeLaw (PB j) qStage) w₁ ≠ ∞)
    (hw₂ : giantSignedStateEnergy PS (fun j => giantSignedTiltedPrimeLaw (PB j) qStage) w₂ ≠ ∞) :
    let ν := fun j => giantSignedTiltedPrimeLaw (PB j) qStage
    let error := (∑ i ∈ patterns, cost i) * ((comparisonCount : ℝ) / (v * Pmin)) +
      (2 * (freshCount : ℝ) * ((n : ℝ) / Pmin)) * ∑ i ∈ patterns, cost i
    ENNReal.ofReal (‖giantSignedRawCleanFamilyPairing PS ν V patterns C κ qSmall ρ θ ζ K w₁ w₂‖ ^ 2) ≤
      ENNReal.ofReal (((1 - (n : ℝ) / Pmin)⁻¹) ^ (Fintype.card B * (k+ell)) *
        (U + error) ^ 2 * L ^ 2) *
        giantSignedStateEnergy PS ν w₁ * giantSignedStateEnergy PS ν w₂ := by
  dsimp only
  let ν := fun j => giantSignedTiltedPrimeLaw (PB j) qStage
  have hnP : (n : ℝ) < Pmin := (div_lt_one hPmin).mp hsmall
  have hν (j : B) (p : PB j) : 0 ≤ ν j p :=
    (giantSignedTiltedPrimeLaw_pos (PB j) qStage (hv.trans_le (hVB j)) hq0
      (fun r => by exact_mod_cast hnP.trans_le (hp j r)) p).le
  let A := giantSignedStateSlotAverage PS w₁
  let B' := giantSignedStateSlotAverage PS w₂
  have hA := giantSignedStateSlotAverage_energy PS hVS ν hν w₁
  have hB := giantSignedStateSlotAverage_energy PS hVS ν hν w₂
  have hAf : giantSignedStateEnergy PS ν A ≠ ∞ := ne_top_of_le_ne_top hw₁ hA
  have hBf : giantSignedStateEnergy PS ν B' ≠ ∞ := ne_top_of_le_ne_top hw₂ hB
  have h := giantSignedBannedTotalClean_pairing_bound PS hVS hP hdis v Pmin hv hPmin hVB hp
    qStage hq0 hq1 hsmall patterns C ζ ρ hρ hρ1 K cost hcost hK freshCount comparisonCount
    hFreshCount hComparisonCount hDensitySmall U hU hOriginal qSmall L hL hSmall
    (fun _ => θ * (κ : ℝ)) markedPhysicalMarkingProduct (giantSignedSmallPrefixProduct_pos hPS)
    (fun _ => κ) A B' hAf hBf (giantSignedStateSlotAverage_bigSymmetric PS w₂)
  have hs : let F := fun d => giantSignedSmallConditioning PS qSmall d A
    let G := fun d => giantSignedEdgeCleanApply PS ν (fun j => markedHarmonicAtom (PB j)) V
      patterns C (θ * (κ : ℝ)) ζ ρ
      (fun i a b aux => if GiantSignedAuxiliaryBan (C i) a b aux then K i a b aux else 0)
      (markedPhysicalMarkingProduct d) κ (giantSignedSmallConditioning PS qSmall d B')
    Summable (fun i : GiantSignedConditionedIndex PS (PB := PB) k ell =>
      (giantSignedConditionedWeight PS ν i : ℂ) *
        star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i) := by
    dsimp only
    simpa only [giantSignedConditionedValue, giantSignedEdgeCleanApply_eq_totalStep] using h.1
  rw [giantSignedRawCleanFamilyPairing_eq_conditioned PS hVS hcross ν V patterns C
    κ qSmall ρ θ ζ K w₁ w₂ hs, giantSignedFullEdgeCleanPairing_eq_totalPairing]
  apply h.2.trans
  gcongr

end
end ArtinMatthews

-- Canonical successor of ArtinMatthews.GiantSignedProjectedRawCleanEnergy

/-! The original projected clean edge is tested against the actual
prefix form, with both endpoint averages and the oriented phase. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedProjectedRawCleanPairing_eq_form
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hcross : ∀ g j, Disjoint (PB g) (PS j))
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (R : ℕ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (f g : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedStatePairing PS ν f
      (giantSignedProjectedRawEdgeFamilyApply R ν V patterns C κ q ρ θ ζ K
        (fun _ => giantSignedRawEdgeCleanMultiplier) g) =
      giantSignedFullCleanForm PS ν ν (fun j => markedHarmonicAtom (PB j))
        patterns C (θ * (κ : ℝ)) ζ ρ q
        (fun i a b aux => if GiantSignedAuxiliaryBan (C i) a b aux then K i a b aux else 0)
        κ (giantSignedStateSlotAverage PS (giantSignedStateMemoryCutoff R f))
          (giantSignedStateSlotAverage PS (giantSignedStateMemoryCutoff R g)) := by
  let F := giantSignedStateMemoryCutoff R f
  let G := giantSignedStateMemoryCutoff R g
  let A := giantSignedStateSlotAverage PS F
  let B' := giantSignedStateSlotAverage PS G
  let μ (j : B) := markedHarmonicAtom (PB j)
  let Kban (i : I) : GiantTwoSidedPatternCoefficient PB (C i) ell :=
    fun a b aux => if GiantSignedAuxiliaryBan (C i) a b aux then K i a b aux else 0
  let H (d : MarkedPhysicalMarking PS k) :=
    giantSignedTotalStepCleanApply PS ν μ patterns C (θ * (κ : ℝ)) ζ ρ Kban
      (markedPhysicalMarkingProduct d) κ (giantSignedSmallConditioning PS q d B')
  have hs := giantSignedConditionedPairing_slotCutoff_summable PS ν R q f H
  unfold giantSignedProjectedRawEdgeFamilyApply
  rw [giantSignedStatePairing_cutoff_right]
  change giantSignedRawCleanFamilyPairing PS ν V patterns C κ q ρ θ ζ K F G =
    giantSignedFullCleanForm PS ν ν μ patterns C (θ * (κ : ℝ)) ζ ρ q Kban κ A B'
  have hs' : Summable (fun i : GiantSignedConditionedIndex PS (PB := PB) k ell =>
    (giantSignedConditionedWeight PS ν i : ℂ) *
      star (giantSignedConditionedValue PS (fun d => giantSignedSmallConditioning PS q d A) i) *
        giantSignedConditionedValue PS (fun d =>
          giantSignedEdgeCleanApply PS ν μ V patterns C (θ * (κ : ℝ)) ζ ρ Kban
            (markedPhysicalMarkingProduct d) κ (giantSignedSmallConditioning PS q d B')) i) := by
    simpa only [giantSignedConditionedValue, giantSignedEdgeCleanApply_eq_totalStep, H] using hs
  rw [giantSignedRawCleanFamilyPairing_eq_conditioned PS hVS hcross ν V patterns C
    κ q ρ θ ζ K F G hs']
  exact giantSignedFullEdgeCleanPairing_eq_form PS hVS ν ν μ V patterns C
    (θ * (κ : ℝ)) ζ ρ q Kban κ A B' hs

theorem giantSignedProjectedRawClean_energy_of_form
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hcross : ∀ g j, Disjoint (PB g) (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    (R : ℕ) (patterns : Finset I) (C : I → B → Finset (Fin k))
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (A : ℝ)
    (hform : ∀ f g : GiantSignedState PS PB (k+ell) → ℂ,
      giantSignedStateEnergy PS ν f ≠ ∞ → giantSignedStateEnergy PS ν g ≠ ∞ →
      (∀ s m, IdealSymmetric (fun a => g (s,a,m))) →
      ENNReal.ofReal (‖giantSignedFullCleanForm PS ν ν (fun j => markedHarmonicAtom (PB j))
        patterns C (θ * (κ : ℝ)) ζ ρ q
        (fun i a b aux => if GiantSignedAuxiliaryBan (C i) a b aux then K i a b aux else 0)
        κ f g‖ ^ 2) ≤ ENNReal.ofReal (A ^ 2) *
          giantSignedStateEnergy PS ν f * giantSignedStateEnergy PS ν g)
    (g : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply R ν V patterns C
      κ q ρ θ ζ K (fun _ => giantSignedRawEdgeCleanMultiplier) g) ≤
      ENNReal.ofReal (A ^ 2) * giantSignedStateEnergy PS ν g := by
  let T := giantSignedProjectedRawEdgeFamilyApply R ν V patterns C
    κ q ρ θ ζ K (fun _ => giantSignedRawEdgeCleanMultiplier) g
  have hT : giantSignedStateEnergy PS ν T ≠ ∞ :=
    giantSignedStateMemoryCutoff_energy_ne_top PS ν R _
  apply giantSignedStateEnergy_le_of_pairing PS hVS ν hν T hT
  intro f _
  let F := giantSignedStateMemoryCutoff R f
  let G := giantSignedStateMemoryCutoff R g
  let Af := giantSignedStateSlotAverage PS F
  let Ag := giantSignedStateSlotAverage PS G
  have hF := giantSignedStateSlotAverage_energy PS hVS ν hν F
  have hG := giantSignedStateSlotAverage_energy PS hVS ν hν G
  have hFfin : giantSignedStateEnergy PS ν Af ≠ ∞ :=
    ne_top_of_le_ne_top (giantSignedStateMemoryCutoff_energy_ne_top PS ν R f) hF
  have hGfin : giantSignedStateEnergy PS ν Ag ≠ ∞ :=
    ne_top_of_le_ne_top (giantSignedStateMemoryCutoff_energy_ne_top PS ν R g) hG
  have he := hform Af Ag hFfin hGfin (giantSignedStateSlotAverage_bigSymmetric PS G)
  change ENNReal.ofReal (‖giantSignedStatePairing PS ν f
    (giantSignedProjectedRawEdgeFamilyApply R ν V patterns C κ q ρ θ ζ K
      (fun _ => giantSignedRawEdgeCleanMultiplier) g)‖ ^ 2) ≤ _
  rw [giantSignedProjectedRawCleanPairing_eq_form PS hVS hcross ν V R patterns C κ q ρ θ ζ K f g]
  refine he.trans ?_
  calc
    _ ≤ ENNReal.ofReal (A ^ 2) * giantSignedStateEnergy PS ν f *
        giantSignedStateEnergy PS ν g :=
      mul_le_mul' (mul_le_mul_right (hF.trans (giantSignedStateMemoryCutoff_energy_le ν R f)) _)
        (hG.trans (giantSignedStateMemoryCutoff_energy_le ν R g))
    _ = _ := mul_right_comm _ _ _

theorem giantSignedProjectedRawClean_energy_of_pairing
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    (R : ℕ) (patterns : Finset I) (C : I → B → Finset (Fin k))
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (A : ℝ≥0∞)
    (hpair : ∀ f g : GiantSignedState PS PB (k+ell) → ℂ,
      giantSignedStateEnergy PS ν f ≠ ∞ → giantSignedStateEnergy PS ν g ≠ ∞ →
      ENNReal.ofReal (‖giantSignedRawCleanFamilyPairing PS ν V patterns C κ q ρ θ ζ K f g‖ ^ 2) ≤
        A * giantSignedStateEnergy PS ν f * giantSignedStateEnergy PS ν g)
    (g : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply R ν V patterns C
      κ q ρ θ ζ K (fun _ => giantSignedRawEdgeCleanMultiplier) g) ≤
      A * giantSignedStateEnergy PS ν g := by
  let T := giantSignedProjectedRawEdgeFamilyApply R ν V patterns C
    κ q ρ θ ζ K (fun _ => giantSignedRawEdgeCleanMultiplier) g
  have hT : giantSignedStateEnergy PS ν T ≠ ∞ :=
    giantSignedStateMemoryCutoff_energy_ne_top PS ν R _
  apply giantSignedStateEnergy_le_of_pairing PS hVS ν hν T hT
  intro f _
  let F := giantSignedStateMemoryCutoff R f
  let G := giantSignedStateMemoryCutoff R g
  have he := hpair F G (giantSignedStateMemoryCutoff_energy_ne_top PS ν R f)
    (giantSignedStateMemoryCutoff_energy_ne_top PS ν R g)
  change ENNReal.ofReal (‖giantSignedStatePairing PS ν f
    (giantSignedProjectedRawEdgeFamilyApply R ν V patterns C κ q ρ θ ζ K
      (fun _ => giantSignedRawEdgeCleanMultiplier) g)‖ ^ 2) ≤ _
  unfold giantSignedProjectedRawEdgeFamilyApply
  rw [giantSignedStatePairing_cutoff_right]
  change ENNReal.ofReal (‖giantSignedRawCleanFamilyPairing PS ν V patterns C κ q ρ θ ζ K F G‖ ^ 2) ≤ _
  refine he.trans ?_
  calc
    _ ≤ A * giantSignedStateEnergy PS ν f * giantSignedStateEnergy PS ν g :=
      mul_le_mul' (mul_le_mul_right (giantSignedStateMemoryCutoff_energy_le ν R f) _)
        (giantSignedStateMemoryCutoff_energy_le ν R g)
    _ = _ := mul_right_comm _ _ _

end
end ArtinMatthews

-- Canonical successor of ArtinMatthews.GiantSignedResidualOrientedClean

/-! Both source orientations use one actual residual pattern family.
The reverse orientation exchanges the two big labels and conjugates
the coefficient before applying the same tilt and ban estimates. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

def giantSignedOrientedCoefficient {G : Type*} {P : G → Finset ℕ}
    {k ell : ℕ} {C : G → Finset (Fin k)} (reverse : Bool)
    (K : GiantTwoSidedPatternCoefficient P C ell) :
    GiantTwoSidedPatternCoefficient P C ell :=
  fun a b aux => if reverse then star (K b a aux) else K a b aux

theorem giantSignedOrientedCoefficient_norm {G : Type*} {P : G → Finset ℕ}
    {k ell : ℕ} {C : G → Finset (Fin k)} (reverse : Bool)
    (K : GiantTwoSidedPatternCoefficient P C ell) {W : ℝ}
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W) (a b : MarkedPhysicalMarking P (k+ell))
    (aux : GiantTwoSidedPatternAuxiliary P C) :
    ‖giantSignedOrientedCoefficient reverse K a b aux‖ ≤ W := by
  cases reverse
  · exact hK a b aux
  · simpa only [giantSignedOrientedCoefficient, if_true, norm_star] using hK b a aux

theorem giantSignedProjectedResidualClean_oriented
    (c₀ C₀ v₀ c d C E N : ℝ) (ell : ℕ)
    (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hv₀ : 0 < v₀) (hc : 0 < c)
    (hd : 0 ≤ d) (hC : 0 ≤ C) (hE : 0 ≤ E) (hell : 1 ≤ ell) :
    ∃ m : ℕ, 1 ≤ m ∧ 0 ≤ idealSourceCostExponent (E+1) C₀ v₀ d C m ∧
      ∀ J : ℕ, idealSourceDimensionThreshold m ell ≤ J →
        ∀ᶠ L : ℝ in atTop, ∀ (G : Type u) [Fintype G] [DecidableEq G]
          (P : G → Finset ℕ) [∀ (j : G) (p : P j), NeZero p.val],
          (∀ g p, p ∈ P g → p.Prime) → Pairwise (fun g j => Disjoint (P g) (P j)) →
          (∀ g, v₀ ≤ bandReciprocalMass (P g)) → (∀ g, IdealPrimeInterval (P g)) →
          (∀ g p, p ∈ P g → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
          c₀*Real.log L ≤ (Fintype.card G : ℝ) → (Fintype.card G : ℝ) ≤ C₀*Real.log L →
          ∃ (G₁ G₂ : Finset G) (hmJ : m ≤ J), Disjoint G₁ G₂ ∧ G₁ ∪ G₂ = univ ∧
            let probes₁ := idealSourceProbes G₁ hmJ
            let probes₂ := idealSourceProbes G₂ hmJ
            let Q := ⌊L^(idealSourceRationalExponent (E+1) C₀ v₀ d m)⌋₊
            let h := L^(-idealSourceWidthExponent (E+1) C₀ v₀ d C m)
            let ξ := L^(-idealSourceThresholdExponent (E+1) C₀ v₀ d C m)
            let patterns := idealResidualPatterns probes₁ probes₂
            (∀ i ∈ patterns, ∀ g, (idealResidualCopied i g).card ≤ m) ∧
            (patterns.card : ℝ) * (1 + ((Q : ℝ)^2 / ξ)^2) ≤
              L^(idealSourceCostExponent (E+1) C₀ v₀ d C m) ∧
            ∀ (S : Type v) [Fintype S] [DecidableEq S] (PS : S → Finset ℕ)
              [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val],
              (∀ j, 0 < bandReciprocalMass (PS j)) →
              (∀ j p, p ∈ PS j → p.Prime) →
              (∀ g j, Disjoint (P g) (PS j)) →
              ∀ (n : ℕ), (n : ℝ) ≤ L^N →
              ∀ (qStage : Fin n → ℝ), (∀ i, 0 ≤ qStage i) → (∀ i, qStage i ≤ 1) →
              ∀ (θ ζ ρ : ℝ), |ζ| ≤ L^C → 0 ≤ ρ → ρ ≤ 1 →
              ∀ (κ : ℤ) (qSmall smallBound : ℝ), 0 ≤ smallBound →
              (∀ f : GiantTwoSidedResidueState PS (J+ell) → ℂ,
                (∑ d : MarkedPhysicalMarking PS J,
                  giantSmallResidueEnergy (giantSmallConditioningMap PS J ell qSmall d f)) ≤
                    smallBound*giantSmallStateEnergy f) →
              ∀ (reverse : Bool) (R : ℕ) (V : G → ℝ)
                (w : GiantSignedState PS P (J+ell) → ℂ),
              let ν := fun j => giantSignedTiltedPrimeLaw (P j) qStage
              let K (i : IdealResidualPattern G J) :=
                giantSignedOrientedCoefficient reverse (idealResidualCoefficient P Q h ξ i)
              giantSignedStateEnergy PS ν
                (giantSignedProjectedRawEdgeFamilyApply R ν V patterns idealResidualCopied
                  κ qSmall ρ θ (if reverse then -ζ else ζ) K
                  (fun _ => giantSignedRawEdgeCleanMultiplier) w) ≤
                ENNReal.ofReal ((L^(-E) * smallBound)^2) * giantSignedStateEnergy PS ν w := by
  have hE' : 0 ≤ E+1 := by linarith
  obtain ⟨m,hm,hC₁,hconstructor⟩ := idealOriginalResidual_construction.{u}
    c₀ C₀ v₀ c d C (E+1) ell hc₀ hC₀ hv₀ hc hd hC hE' hell
  refine ⟨m,hm,hC₁,?_⟩
  intro J hJ
  filter_upwards [hconstructor J hJ,
    giantSignedResidualBudget_eventually v₀ c (E+1) C₀ N
      (idealSourceCostExponent (E+1) C₀ v₀ d C m) m J ell hv₀ hc hC₀,
    eventually_ge_atTop (2 : ℝ)] with L hconstructed hbudget hL
  intro G _ _ P _ hprime hdisP hV hinterval hband hcardLo hcardHi
  obtain ⟨G₁,G₂,hmJ,hdis,hunion,hcap,hconstant,_hselectors,henergy⟩ :=
    hconstructed G P hprime hdisP hV hinterval hband hcardLo hcardHi
  refine ⟨G₁,G₂,hmJ,hdis,hunion,hcap,hconstant,?_⟩
  dsimp only
  intro S _ _ PS _ hVS hPS hcross n hn qStage hq0 hq1 θ ζ ρ hζ hρ hρ1
    κ qSmall smallBound hsmallBound hSmall reverse R V w
  let probes₁ := idealSourceProbes G₁ hmJ
  let probes₂ := idealSourceProbes G₂ hmJ
  let patterns := idealResidualPatterns probes₁ probes₂
  let Q := ⌊L^(idealSourceRationalExponent (E+1) C₀ v₀ d m)⌋₊
  let h := L^(-idealSourceWidthExponent (E+1) C₀ v₀ d C m)
  let ξ := L^(-idealSourceThresholdExponent (E+1) C₀ v₀ d C m)
  let K : ∀ ν : IdealResidualPattern G J,
      GiantTwoSidedPatternCoefficient P (idealResidualCopied ν) ell :=
    idealResidualCoefficient P Q h ξ
  let cost : IdealResidualPattern G J → ℝ := fun _ => 1+((Q : ℝ)^2/ξ)^2
  let U := L^(-(E+1))
  let fresh := Fintype.card G*(m+ell)
  let comparisons := (Fintype.card G*m)*(2*(J+ell))
  let Pmin := Real.exp (L^c)
  let error := (∑ ν∈patterns, cost ν)*((comparisons : ℝ)/(v₀*Pmin))+
    (2*(fresh : ℝ)*((n : ℝ)/Pmin))*∑ ν∈patterns, cost ν
  have hLpos : 0 < L := by linarith
  have hU : 0 ≤ U := Real.rpow_nonneg hLpos.le _
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hLpos _
  have hcost (ν : IdealResidualPattern G J) : 0 ≤ cost ν := by dsimp [cost]; positivity
  have hcostSum : (∑ ν∈patterns, cost ν) ≤
      L^(idealSourceCostExponent (E+1) C₀ v₀ d C m) := by
    simpa only [patterns,probes₁,probes₂,cost,Q,ξ,sum_const,nsmul_eq_mul] using hconstant
  obtain ⟨hsmall,hFreshSmall,hDimSmall,herror⟩ :=
    hbudget (Fintype.card G) n (∑ ν∈patterns, cost ν) hcardHi hn hcostSum
  have herror0 : 0 ≤ error := by dsimp [error]; positivity
  have herrorU : error ≤ U/4 := by
    simpa only [error,Pmin,fresh,comparisons,U,mul_assoc] using herror
  let ν (j : G) := giantSignedTiltedPrimeLaw (P j) qStage
  let K' (i : IdealResidualPattern G J) :=
    giantSignedOrientedCoefficient reverse (K i)
  let ζ' := if reverse then -ζ else ζ
  have hVpos (j : G) : 0 < bandReciprocalMass (P j) := hv₀.trans_le (hV j)
  have hnP : (n : ℝ) < Pmin := (div_lt_one (Real.exp_pos _)).mp hsmall
  have hν (j : G) (p : P j) : 0 ≤ ν j p := by
    apply (giantSignedTiltedPrimeLaw_pos (P j) qStage (hVpos j) hq0 _ p).le
    intro a
    exact_mod_cast hnP.trans_le (hband j a.val a.property).1
  have hForward (Θ : ℝ) (f : MarkedPhysicalMarking P (J+ell) → ℂ) :
      idealLabelEnergy P (J+ell) (idealOperator patterns idealResidualCopied Θ ζ K f) ≤
        U^2 * idealLabelEnergy P (J+ell) f := by
    simpa only [U,K,Q,h,ξ,patterns,probes₁,probes₂,idealResidualOperator] using
      henergy Θ ζ hζ f
  have hOriginal (Θ : ℝ) (f : MarkedPhysicalMarking P (J+ell) → ℂ)
      (_hf : IdealSymmetric f) :
      idealLabelEnergy P (J+ell) (idealOperator patterns idealResidualCopied Θ ζ' K' f) ≤
        U^2 * idealLabelEnergy P (J+ell) f := by
    cases reverse
    · exact hForward Θ f
    · have hreverse : K' = fun i a b aux => star (K i b a aux) := by
        funext i a b aux
        simp [K',giantSignedOrientedCoefficient]
      have hfreq : ζ' = -ζ := by simp [ζ']
      rw [hreverse, hfreq]
      simpa only [neg_neg] using idealOperator_reverse_energy_le P hVpos patterns idealResidualCopied
        (-Θ) ζ K U (hForward (-Θ)) f
  have hK' (i : IdealResidualPattern G J) (a b : MarkedPhysicalMarking P (J+ell))
      (aux : GiantTwoSidedPatternAuxiliary P (idealResidualCopied i)) :
      ‖K' i a b aux‖ ≤ cost i :=
    giantSignedOrientedCoefficient_norm reverse (K i)
      (idealResidualCoefficient_norm P Q h hξ i) a b aux
  have hscalar : ((1-(n : ℝ)/Pmin)⁻¹)^(Fintype.card G*(J+ell))*(U+error)^2 ≤
      (L^(-E))^2 := by
    have ht := giantSignedCleanScalar_two ((n : ℝ)/Pmin) U error
      (Fintype.card G*(J+ell)) (by dsimp [Pmin]; positivity) hsmall hDimSmall hU herror0 herrorU
    have hUeq : U = L^(-E)/L := by
      dsimp only [U]
      rw [show -(E+1)=-E+(-1) by ring,Real.rpow_add hLpos,Real.rpow_neg_one]
      rfl
    have htwo : 2*U ≤ L^(-E) := by
      rw [hUeq]
      calc
        _ = (2*L^(-E))/L := by ring
        _ ≤ L^(-E) := (div_le_iff₀ hLpos).mpr (by
          nlinarith [mul_nonneg (Real.rpow_nonneg hLpos.le (-E)) (sub_nonneg.mpr hL)])
    exact ht.trans (pow_le_pow_left₀ (mul_nonneg (by norm_num) hU) htwo 2)
  have hfactor : ((1-(n : ℝ)/Pmin)⁻¹)^(Fintype.card G*(J+ell))*(U+error)^2*smallBound^2 ≤
      (L^(-E)*smallBound)^2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hscalar (sq_nonneg smallBound)
  refine giantSignedProjectedRawClean_energy_of_pairing PS hVS ν hν V R patterns
    idealResidualCopied κ qSmall ρ θ ζ' K' (ENNReal.ofReal ((L^(-E)*smallBound)^2)) ?_ w
  intro f g hf hg
  have hp := giantSignedBannedRawCleanFamilyPairing_energy PS (k:=J) (ell:=ell)
    hVS hPS hcross hprime hdisP v₀ Pmin hv₀ (Real.exp_pos _) hV
    (fun j p => (hband j p.val p.property).1) qStage hq0 hq1 hsmall
    V patterns idealResidualCopied θ ζ' ρ κ hρ hρ1 K' cost (fun i _ => hcost i)
    (fun i _ => hK' i) fresh comparisons
    (fun i hi => idealSourceResidual_freshCount G₁ G₂ hmJ i hi)
    (fun i hi => idealSourceResidual_comparisonCount G₁ G₂ hmJ i hi)
    hFreshSmall U hU hOriginal qSmall smallBound hsmallBound hSmall f g hf hg
  refine hp.trans ?_
  exact mul_le_mul_left (mul_le_mul_left (ENNReal.ofReal_le_ofReal hfactor) _) _

end
end ArtinMatthews
