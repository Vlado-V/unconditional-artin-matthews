module

public import ArtinMatthews.GiantSmallStatePairing


set_option backward.privateInPublic true
@[expose] public section

/-! The actual common-prefix small-state kernel has exactly the P_d
bilinear form, including its two half-dampings and original Haar mass. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val]

def giantSmallCanonicalPairing (q : ℝ)
    (w₁ w₂ : GiantTwoSidedResidueState P (k+ell) → ℂ)
    (H : MarkedPhysicalMarking P k → GiantTwoSidedFullResidue P →
      GiantTwoSidedFullResidue P → ℂ) : ℂ :=
  ∑ s : GiantTwoSidedResidueState P (k+ell), ∑ t : GiantTwoSidedResidueState P (k+ell),
    star (w₁ s) * (if giantSmallPrefix t.val.2 = giantSmallPrefix s.val.2 then
      ((giantTwoSidedResidueHaarStateMass P (k+ell) * giantSmallTailMass P ell *
        giantTwoSidedResidueDamping P (k+ell) q s.val.1 *
        giantTwoSidedResidueDamping P (k+ell) q t.val.1 : ℝ) : ℂ) *
        H (giantSmallPrefix s.val.2) s.val.1 t.val.1 else 0) * w₂ t

theorem giantSmallCanonicalPairing_eq_conditioned
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (q : ℝ)
    (w₁ w₂ : GiantTwoSidedResidueState P (k+ell) → ℂ)
    (H : MarkedPhysicalMarking P k → GiantTwoSidedFullResidue P →
      GiantTwoSidedFullResidue P → ℂ) :
    giantSmallCanonicalPairing q w₁ w₂ H =
      ∑ d : MarkedPhysicalMarking P k, ∑ y : GiantTwoSidedFullResidue P,
        ∑ y' : GiantTwoSidedFullResidue P,
          ((Fintype.card (GiantTwoSidedFullResidue P) : ℝ)⁻¹ : ℂ) *
            star (giantSmallConditioningMap P k ell q d w₁ y) * H d y y' *
              giantSmallConditioningMap P k ell q d w₂ y' := by
  let W (y y' : GiantTwoSidedFullResidue P) : ℂ :=
    ((giantTwoSidedResidueHaarStateMass P (k+ell) * giantSmallTailMass P ell *
      giantTwoSidedResidueDamping P (k+ell) q y *
      giantTwoSidedResidueDamping P (k+ell) q y' : ℝ) : ℂ)
  let F (d : MarkedPhysicalMarking P k) (y y' : GiantTwoSidedFullResidue P)
      (r r' : MarkedPhysicalMarking P ell) : ℂ :=
    W y y' * star (giantSmallStateValue w₁ y (giantSmallAppend d r)) * H d y y' *
      giantSmallStateValue w₂ y' (giantSmallAppend d r')
  have hExpand : giantSmallCanonicalPairing q w₁ w₂ H =
      ∑ y : GiantTwoSidedFullResidue P, ∑ y' : GiantTwoSidedFullResidue P,
        ∑ a : MarkedPhysicalMarking P (k+ell), ∑ b : MarkedPhysicalMarking P (k+ell),
          if giantSmallPrefix b = giantSmallPrefix a then
            W y y' * star (giantSmallStateValue w₁ y a) * H (giantSmallPrefix a) y y' *
              giantSmallStateValue w₂ y' b else 0 := by
    unfold giantSmallCanonicalPairing
    change (∑ s : GiantTwoSidedResidueState P (k+ell),
      ∑ t : GiantTwoSidedResidueState P (k+ell), star (w₁ s) *
        (if giantSmallPrefix t.val.2 = giantSmallPrefix s.val.2 then
          W s.val.1 t.val.1 * H (giantSmallPrefix s.val.2) s.val.1 t.val.1 else 0) * w₂ t) = _
    rw [giantSmallState_pairing_expand w₁ w₂ (fun y a y' b =>
      if giantSmallPrefix b = giantSmallPrefix a then
        W y y' * H (giantSmallPrefix a) y y' else 0)]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y' _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : giantSmallPrefix b = giantSmallPrefix a
    · simp only [h, ite_true, W]
      ring
    · simp only [h, ite_false, mul_zero, zero_mul]
  have hCopied (y y' : GiantTwoSidedFullResidue P) :
      (∑ a : MarkedPhysicalMarking P (k+ell), ∑ b : MarkedPhysicalMarking P (k+ell),
        if giantSmallPrefix b = giantSmallPrefix a then
          W y y' * star (giantSmallStateValue w₁ y a) * H (giantSmallPrefix a) y y' *
            giantSmallStateValue w₂ y' b else 0) =
      ∑ d : MarkedPhysicalMarking P k, ∑ r : MarkedPhysicalMarking P ell,
        ∑ r' : MarkedPhysicalMarking P ell, F d y y' r r' := by
    rw [giantSmallCopiedPair_sum]
    simp only [giantSmallPrefix_append, F]
  rw [hExpand]
  simp_rw [hCopied]
  have hOrder :
      (∑ y : GiantTwoSidedFullResidue P, ∑ y' : GiantTwoSidedFullResidue P,
        ∑ d : MarkedPhysicalMarking P k, ∑ r : MarkedPhysicalMarking P ell,
          ∑ r' : MarkedPhysicalMarking P ell, F d y y' r r') =
      ∑ d : MarkedPhysicalMarking P k, ∑ y : GiantTwoSidedFullResidue P,
        ∑ y' : GiantTwoSidedFullResidue P, ∑ r : MarkedPhysicalMarking P ell,
          ∑ r' : MarkedPhysicalMarking P ell, F d y y' r r' := by
    calc
      _ = ∑ y : GiantTwoSidedFullResidue P, ∑ d : MarkedPhysicalMarking P k,
          ∑ y' : GiantTwoSidedFullResidue P, ∑ r : MarkedPhysicalMarking P ell,
            ∑ r' : MarkedPhysicalMarking P ell, F d y y' r r' := by
        apply Finset.sum_congr rfl
        intro y _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hOrder]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro y' _
  have hh := congrArg (fun z : ℂ =>
    ((Fintype.card (GiantTwoSidedFullResidue P) : ℝ)⁻¹ : ℂ) * z)
    (giantSmallConditioningMap_pair hV q q d w₁ w₂ y y' (H d y y'))
  have hmass : giantTwoSidedResidueHaarStateMass P (k+ell) * giantSmallTailMass P ell =
      (Fintype.card (GiantTwoSidedFullResidue P) : ℝ)⁻¹ *
        (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) * giantSmallTailMass P ell) := by
    rw [giantTwoSidedResidueHaarStateMass_eq]
    simp only [div_eq_mul_inv]
    ring
  simpa only [F, W, hmass, Finset.mul_sum, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, mul_assoc] using hh.symm

end
end ArtinMatthews
