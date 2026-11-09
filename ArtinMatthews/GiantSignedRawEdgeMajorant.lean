module

public import ArtinMatthews.GiantSignedRawEdgeData
public import ArtinMatthews.GiantSignedSmallEdgeKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The absolute comparison retains the original raw coefficient on
its left side and uses the actual small and store/promote kernels. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    {C : B → Finset (Fin k)}

omit [DecidableEq S] [DecidableEq B] in
theorem giantSignedRawEdgeProduct_pos
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    0 < giantSignedRawEdgeProduct s r := by
  unfold giantSignedRawEdgeProduct
  apply Nat.mul_pos
  · exact Finset.prod_pos (fun j _ => Finset.prod_pos (fun i _ =>
      (hPS j _ ((giantSignedRawEdgeSmallSource s r).val.2 j (Fin.castAdd ell i)).property).pos))
  · apply Nat.mul_pos
    · unfold giantTwoSidedPatternCopiedProduct
      exact Finset.prod_pos (fun j _ => Finset.prod_pos (fun i _ =>
        (hPB j _ (giantSignedRawEdgeBigSource s r j (Fin.castAdd ell i)).property).pos))
    · unfold giantTwoSidedPatternAuxiliaryProduct
      exact Finset.prod_pos (fun j _ => Finset.prod_pos (fun i _ =>
        (hPB j _ (r.auxiliary j i).property).pos))

theorem giantSignedRawEdgeCoefficient_norm_le
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) {q : ℝ} (hq : 0 ≤ q)
    (ρ θ ζ W : ℝ) (hW : 0 ≤ W) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    ‖giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r‖ ≤
      if IdealCopied C (giantSignedRawEdgeBigSource s r) r.bigTarget then
        giantTwoSidedResidueSlotNormalization (J := S) (k+ell) *
          giantTwoSidedResidueSlotNormalization (J := B) (k+ell) *
          giantTwoSidedPatternAuxiliaryMass r.auxiliary * W *
          giantSignedSmallEdgeWeight κ
            (giantTwoSidedPatternCopiedProduct C (giantSignedRawEdgeBigSource s r) *
              giantTwoSidedPatternAuxiliaryProduct r.auxiliary) q
            (giantSignedRawEdgeSmallSource s r) r.smallTarget *
          ‖giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ
            (κ * (giantSignedRawEdgeProduct s r : ℤ)) (giantSignedRawEdgeProduct s r)
            (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r))
            (giantSignedPatternFreeLabels C r.bigTarget) s.2.2 r.choice‖
      else 0 := by
  let NS := giantTwoSidedResidueSlotNormalization (J := S) (k+ell)
  let NB := giantTwoSidedResidueSlotNormalization (J := B) (k+ell)
  have hNS : 0 ≤ NS := inv_nonneg.mpr (sq_nonneg _)
  have hNB : 0 ≤ NB := inv_nonneg.mpr (sq_nonneg _)
  have hNSraw : 0 ≤ giantTwoSidedResidueSlotNormalization (J := S) (k+ell) := hNS
  have hNBraw : 0 ≤ giantTwoSidedResidueSlotNormalization (J := B) (k+ell) := hNB
  have haux := giantTwoSidedPatternAuxiliaryMass_nonneg hVB r.auxiliary
  have htail : 0 ≤ giantSmallTailMass PS ell :=
    Finset.prod_nonneg (fun j _ => pow_nonneg (inv_nonneg.mpr (hVS j).le) _)
  have hdamp (y : GiantTwoSidedFullResidue PS) :
      0 ≤ giantTwoSidedResidueDamping PS (k+ell) q y := Real.rpow_nonneg hq _
  have hsmall := giantSignedSmallEdgeWeight_nonneg κ
    (giantTwoSidedPatternCopiedProduct C (giantSignedRawEdgeBigSource s r) *
      giantTwoSidedPatternAuxiliaryProduct r.auxiliary) q
      (giantSignedRawEdgeSmallSource s r) r.smallTarget
  by_cases hr : GiantSignedRawEdgeCondition κ s r
  · have hcopy := hr.2.2.1
    rw [ite_eq_left hcopy]
    have hs : giantSignedSmallEdgeWeight κ
        (giantTwoSidedPatternCopiedProduct C (giantSignedRawEdgeBigSource s r) *
          giantTwoSidedPatternAuxiliaryProduct r.auxiliary) q
          (giantSignedRawEdgeSmallSource s r) r.smallTarget =
        giantSmallTailMass PS ell *
          giantTwoSidedResidueDamping PS (k+ell) q (giantSignedRawEdgeSmallSource s r).val.1 *
          giantTwoSidedResidueDamping PS (k+ell) q r.smallTarget.val.1 := by
      rw [giantSignedSmallEdgeWeight_eq hPS hVS κ _ hq]
      exact ite_eq_left ⟨hr.1, hr.2.1⟩
    have hphase : ‖(giantSignedRawEdgeProduct s r : ℂ) ^ ((ζ : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (giantSignedRawEdgeProduct_pos hPS hPB s r)]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, mul_zero, zero_mul, sub_self, Real.rpow_zero]
    have ht : ‖∏ g : S, ((bandReciprocalMass (PS g))⁻¹ : ℂ) ^ ell‖ =
        giantSmallTailMass PS ell := by
      simp only [norm_prod, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        giantSmallTailMass]
      apply Finset.prod_congr rfl
      intro g _
      rw [abs_of_pos (hVS g)]
    rw [giantSignedRawEdgeCoefficient, ite_eq_left hr, hs]
    simp only [norm_mul, ht, hphase, idealAdditivePhase_norm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hNSraw, abs_of_nonneg hNBraw, abs_of_nonneg haux,
      abs_of_nonneg (hdamp _), mul_one]
    let Z := ‖giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ
      (κ * (giantSignedRawEdgeProduct s r : ℤ)) (giantSignedRawEdgeProduct s r)
      (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r))
      (giantSignedPatternFreeLabels C r.bigTarget) s.2.2 r.choice‖
    let A := NS * NB * giantTwoSidedPatternAuxiliaryMass r.auxiliary *
      giantSmallTailMass PS ell *
      giantTwoSidedResidueDamping PS (k+ell) q (giantSignedRawEdgeSmallSource s r).val.1 *
      giantTwoSidedResidueDamping PS (k+ell) q r.smallTarget.val.1 * Z
    have hA : 0 ≤ A := mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hNS hNB) haux) htail)
        (hdamp _)) (hdamp _)) (norm_nonneg _)
    calc
      _ = A * ‖K (giantSignedRawEdgeBigSource s r) r.bigTarget r.auxiliary‖ := by
        dsimp [A,Z,NS,NB]
        ring
      _ ≤ A * W := mul_le_mul_of_nonneg_left (hK _ _ _) hA
      _ = _ := by dsimp [A,Z,NS,NB]; ring
  · rw [giantSignedRawEdgeCoefficient, ite_eq_right hr, norm_zero]
    split_ifs
    · change 0 ≤ NS * NB * _ * _ * _ * _
      positivity
    · exact le_rfl

end
end ArtinMatthews
