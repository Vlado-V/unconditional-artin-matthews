module

public import ArtinMatthews.GiantSignedRawCoreData
public import ArtinMatthews.GiantSignedRawEdgeEnumeration
public import ArtinMatthews.GiantSignedEdgeSquare


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical positive section sums the original target lists through
their copied-coordinate fibers and the literal ordered edge choices. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedCopiedTarget_plain_sum {J R : Type*} [Fintype J] [DecidableEq J]
    [AddCommMonoid R] {P : J → Finset ℕ} {k ell : ℕ}
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell))
    (F : MarkedPhysicalMarking P (k+ell) → R) :
    (∑ t : GiantSignedPrimeTuple P (fun j => ell + (C j).card),
      F (giantSignedPatternFill C a t)) =
      ∑ b : MarkedPhysicalMarking P (k+ell), if IdealCopied C a b then F b else 0 := by
  have he := (giantSignedCopiedTargetEquiv C a).sum_comp (fun b => F b.val)
  have hs := Finset.sum_subtype (p := IdealCopied C a) (F := inferInstance)
    (Finset.univ.filter (IdealCopied C a)) (by simp) F
  exact he.trans (by simpa only [Finset.sum_filter] using hs.symm)

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

def giantSignedRawPositiveSection (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ : ℝ) (aux : GiantTwoSidedPatternAuxiliary PB C)
    (τS : S → Equiv.Perm (Fin (k+ell))) (τB : B → Equiv.Perm (Fin (k+ell)))
    (f : GiantSignedState PS PB (k+ell) → ℝ)
    (s : GiantTwoSidedResidueState PS (k+ell)) (a : MarkedPhysicalMarking PB (k+ell))
    (m : GiantSignedMemory PB) : ℝ :=
  let D := giantSignedSmallPrefixProduct s *
    (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux)
  ∑ z : GiantTwoSidedResidueState PS (k+ell),
    giantSignedSmallEdgeWeight κ
      (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux) q s z *
      ∑ c : GiantSignedEdgeChoice (fun g => ell + (C g).card) m.1,
        ∑ b : MarkedPhysicalMarking PB (k+ell),
          if IdealCopied C a b then
            ‖giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ (κ * (D : ℤ)) D
              (giantSignedPatternFreeLabels C a) (giantSignedPatternFreeLabels C b) m c‖ *
              f ((giantTwoSidedResiduePermute τS).symm z,
                (giantSignedGroupedTuplePermutation τB).symm b,
                giantSignedEdgeTarget (κ * (D : ℤ)) m (giantSignedPatternFreeLabels C a) c)
          else 0

theorem giantSignedRawPositiveSection_eq_core_norm
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) (hV : ∀ g, 0 < V g)
    (κ : ℤ) (q : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (aux : GiantTwoSidedPatternAuxiliary PB C)
    (τS : S → Equiv.Perm (Fin (k+ell))) (τB : B → Equiv.Perm (Fin (k+ell)))
    (f : GiantSignedState PS PB (k+ell) → ℝ) (hf : ∀ s, 0 ≤ f s)
    (s : GiantTwoSidedResidueState PS (k+ell)) (a : MarkedPhysicalMarking PB (k+ell))
    (m : GiantSignedMemory PB) :
    giantSignedRawPositiveSection ν V κ q ρ aux τS τB f s a m =
      ‖giantSignedRawCoreApply ν V κ q ρ aux
        (fun t => (f ((giantTwoSidedResiduePermute τS).symm t.1,
          (giantSignedGroupedTuplePermutation τB).symm t.2.1, t.2.2) : ℂ)) (s,a,m)‖ := by
  let D := giantSignedSmallPrefixProduct s *
    (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux)
  let F (z : GiantTwoSidedResidueState PS (k+ell))
      (b : MarkedPhysicalMarking PB (k+ell)) (out : GiantSignedMemory PB) : ℝ :=
    f ((giantTwoSidedResiduePermute τS).symm z,
      (giantSignedGroupedTuplePermutation τB).symm b, out)
  have hlabels (z : GiantTwoSidedResidueState PS (k+ell))
      (c : GiantSignedEdgeChoice (fun g => ell + (C g).card) m.1) :
      (∑ b : MarkedPhysicalMarking PB (k+ell),
        if IdealCopied C a b then
          ‖giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ (κ * (D : ℤ)) D
            (giantSignedPatternFreeLabels C a) (giantSignedPatternFreeLabels C b) m c‖ *
            F z b (giantSignedEdgeTarget (κ * (D : ℤ)) m (giantSignedPatternFreeLabels C a) c)
        else 0) =
        ∑ b : GiantSignedPrimeTuple PB (fun g => ell + (C g).card),
          ‖giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ (κ * (D : ℤ)) D
            (giantSignedPatternFreeLabels C a) b m c‖ *
            F z (giantSignedPatternFill C a b)
              (giantSignedEdgeTarget (κ * (D : ℤ)) m (giantSignedPatternFreeLabels C a) c) := by
    rw [← giantSignedCopiedTarget_plain_sum C a]
    simp only [giantSignedPatternFreeLabels_fill]
  unfold giantSignedRawPositiveSection
  change (∑ z : GiantTwoSidedResidueState PS (k+ell),
    giantSignedSmallEdgeWeight κ
      (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux) q s z *
      ∑ c : GiantSignedEdgeChoice (fun g => ell + (C g).card) m.1,
        ∑ b : MarkedPhysicalMarking PB (k+ell),
          if IdealCopied C a b then
            ‖giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ (κ * (D : ℤ)) D
              (giantSignedPatternFreeLabels C a) (giantSignedPatternFreeLabels C b) m c‖ *
              F z b (giantSignedEdgeTarget (κ * (D : ℤ)) m (giantSignedPatternFreeLabels C a) c)
          else 0) = _
  simp_rw [hlabels]
  have hedge (z : GiantTwoSidedResidueState PS (k+ell)) :=
    giantSignedEdgeApply_nonnegative_norm ν hν V hV hρ (κ * (D : ℤ)) D
      (giantSignedPatternFreeLabels C a)
      (fun b out => F z (giantSignedPatternFill C a b) out) (fun _ _ => hf _) m
  simp_rw [← hedge]
  symm
  exact giantSignedSmallFreeEdgeApply_ofReal_norm ν hν V (fun g => (hV g).le) κ q hρ
    (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux)
    (fun z b out => F z (giantSignedPatternFill C a b) out) (fun _ _ _ => hf _)
    s (giantSignedPatternFreeLabels C a) m

end
end ArtinMatthews
