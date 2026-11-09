module

public import ArtinMatthews.GiantCandidatePerformedFourier
public import ArtinMatthews.GiantSignedSourceReturnScalars
public import ArtinMatthews.GiantSignedCappedBoundaryRank


set_option backward.privateInPublic true
@[expose] public section

/-! Return integration and normalization on the literal performed
group carrier of the physical root statistic. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem giantCandidatePerformedIndependentMoment_norm_of_trace {I : Type} {x : ℝ}
    (groups : Finset (GiantCandidateGroupIndex x))
    [∀ p : ↥(markedPhysicalBandPrimes (fun j : ↥groups => giantCandidateGroup x j.val)), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes (giantCandidatePerformedSmallBand groups)), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes (Sum.elim (giantCandidatePerformedSmallBand groups)
      (giantCandidatePerformedBigBand groups))), NeZero p.val]
    (hdis : Pairwise (fun i j : ↥groups => Disjoint (giantCandidateGroup x i.val) (giantCandidateGroup x j.val)))
    {k ell n : ℕ} (patterns : Fin n → Finset I)
    (C : Fin n → I → GiantCandidatePerformedBig groups → Finset (Fin k)) (κ : Fin n → ℤ)
    (q ρ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i p, GiantTwoSidedPatternCoefficient (giantCandidatePerformedBigBand groups) (C i p) ell)
    {δ : ℝ} :
    let PS := giantCandidatePerformedSmallBand groups
    let PB := giantCandidatePerformedBigBand groups
    let visitQ := giantSignedSourceVisitQ q n
    let ν := fun g => giantSignedTiltedPrimeLaw (PB g) visitQ
    let V := fun g => bandReciprocalMass (PB g)
    let base := ∏ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeBaseline visitQ p.val
    let U (θ : ℝ) := giantSignedGuardedTraceBoundaryPairing (PS := PS) (k := k) (ell := ell) ν
      (giantSignedChronologicalTraceRows (PS := PS) (k := k) (ell := ell) ν V q ρ θ
        n patterns C κ visitQ ζ K (fun _ _ _ _ => 1))
      (giantSignedTraceBirthDistinctIndicator (PS := PS) (k := k) (ell := ell) ν V q ρ θ
        n patterns C κ visitQ ζ K (fun _ _ _ _ => 1))
    0 ≤ base → base ≤ 1 →
    (∀ θ : ℝ, giantTwoSidedExpandedIndependentFourierMoment patterns
      (fun i p => giantSignedJoinedPattern (S := GiantCandidatePerformedSmall groups) (C i p)) κ q ζ
      (fun i p => giantSignedJoinedCoefficient (PS := PS) (K i p)) (θ : AddCircle (1 : ℝ)) =
      (base : ℂ)*U θ) →
    (∀ θ, ‖U θ‖ ≤ δ) →
    ‖giantTwoSidedExpandedIndependentMoment patterns (fun i p => giantCandidatePerformedPattern groups (C i p))
      κ q ζ (fun i p => giantCandidatePerformedCoefficient groups (K i p))‖ ≤ δ := by
  intro PS PB visitQ ν V base U hbase0 hbase1 htrace hbound
  rw [giantTwoSidedExpandedIndependentMoment_unitInterval]
  have hpoint (θ : ℝ) : ‖giantTwoSidedExpandedIndependentFourierMoment patterns
      (fun i p => giantCandidatePerformedPattern groups (C i p)) κ q ζ
      (fun i p => giantCandidatePerformedCoefficient groups (K i p)) (θ : AddCircle (1 : ℝ))‖ ≤ δ := by
    rw [giantCandidatePerformedFourier_eq_split groups hdis patterns C κ q ζ K, htrace θ,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hbase0]
    exact (mul_le_of_le_one_left (norm_nonneg _) hbase1).trans (hbound θ)
  simpa only [sub_zero, abs_one, mul_one] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (fun θ _ => hpoint θ))

theorem giantCandidatePerformedPhysicalMoment_norm_div_le {I : Type*} {x : ℝ}
    (groups : Finset (GiantCandidateGroupIndex x))
    [∀ p : ↥(markedPhysicalBandPrimes (fun j : ↥groups => giantCandidateGroup x j.val)), NeZero p.val]
    {k ell n : ℕ} (patterns : Fin n → Finset I)
    (C : Fin n → I → GiantCandidatePerformedBig groups → Finset (Fin k)) (κ : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i p, GiantTwoSidedPatternCoefficient (giantCandidatePerformedBigBand groups) (C i p) ell)
    (X : ℝ) {A B : ℝ} :
    let c := fun i p => giantCandidatePerformedPattern groups (C i p)
    let u := fun i p => giantCandidatePerformedCoefficient groups (K i p)
    let len := ((⌈2*X⌉₊-⌈X⌉₊ : ℕ) : ℝ)
    let P := giantTwoSidedExpandedPhysicalMoment patterns c κ q ζ u
      (giantTwoSidedRootInterval X) (giantTwoSidedRootSlice X)
    let Q := giantTwoSidedExpandedIndependentMoment patterns c κ q ζ u
    0 < len → ‖P-(len : ℂ)*Q‖/len ≤ A → ‖Q‖ ≤ B → ‖P‖/len ≤ A+B := by
  intro c u len P Q hlen herr hQ
  have htri : ‖P‖ ≤ ‖P-(len : ℂ)*Q‖ + ‖(len : ℂ)*Q‖ := by
    simpa only [sub_add_cancel] using norm_add_le (P-(len : ℂ)*Q) ((len : ℂ)*Q)
  calc
    _ ≤ (‖P-(len : ℂ)*Q‖ + ‖(len : ℂ)*Q‖)/len := div_le_div_of_nonneg_right htri hlen.le
    _ = ‖P-(len : ℂ)*Q‖/len + ‖Q‖ := by
      rw [add_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlen.le, mul_comm len,
        mul_div_cancel_right₀ _ hlen.ne']
    _ ≤ _ := add_le_add herr hQ

end
end ArtinMatthews
