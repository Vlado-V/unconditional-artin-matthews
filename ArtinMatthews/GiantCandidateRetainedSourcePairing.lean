module

public import ArtinMatthews.GiantCandidateSourceAlternation
public import ArtinMatthews.GiantCandidatePhysicalEndpointPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The selected residual family gives the physical endpoint pairing
on each dyad. The retained threshold precedes the family choices. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem giantCandidateRetainedSourcePairing_of_memory_identity
    {Jtest : Type*} [Fintype Jtest] (e : Jtest → ℝ) (he : ∀ j, 0 < e j ∧ e j < 1)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) {mχ : ℕ} (χ : DirichletCharacter ℂ mχ)
    (threshold C Cstep E γ τ : ℝ) (hthreshold : 0 < threshold) (ell j : ℕ)
    (hell : 1 ≤ ell) (hj : 0 < j) {q ρ : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hqρ : Real.sqrt q < ρ^2)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hγ : 0 < γ) (hτ : 0 < τ)
    (hIdentity : ∀ {x : ℝ} (groups : Finset (GiantCandidateGroupIndex x)),
      let PS := giantCandidatePerformedSmallBand groups
      let PB := giantCandidatePerformedBigBand groups
      ∀ [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
        [∀ p : ↥(markedPhysicalBandPrimes PB), NeZero p.val]
        [∀ g, ∀ p : PB g, NeZero p.val]
        [∀ p : ↥(markedPhysicalBandPrimes (Sum.elim PS PB)), NeZero p.val],
      (∀ j p, p ∈ PS j → p.Prime) → (∀ j p, p ∈ PB j → p.Prime) →
      (Pairwise fun i j => Disjoint (PS i) (PS j)) → (Pairwise fun i j => Disjoint (PB i) (PB j)) →
      (∀ i j, Disjoint (PS i) (PB j)) →
      (∀ j, 0 < bandReciprocalMass (PS j)) → (∀ j, 0 < bandReciprocalMass (PB j)) →
      ∀ (I : Type) {k n : ℕ}, n ≠ 0 →
      let visitQ := giantSignedSourceVisitQ q n
      let ν := fun g => giantSignedTiltedPrimeLaw (PB g) visitQ
      let V := fun g => bandReciprocalMass (PB g)
      (∀ p : ↥(markedPhysicalBandPrimes PB), 0 < giantSignedPrimeBaseline visitQ p.val) →
      ∀ (patterns : Fin n → Finset I) (copied : Fin n → I → GiantCandidatePerformedBig groups → Finset (Fin k))
        (κ : Fin n → ℤ), (∀ i, 0 < (κ i).natAbs) →
        (∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p) →
      ∀ (ζ : Fin n → ℝ) (K : ∀ i p, GiantTwoSidedPatternCoefficient PB (copied i p) ell)
        (θ : ℝ),
      let rows := giantSignedChronologicalTraceRows (PS := PS) (k := k) (ell := ell)
        ν V q ρ θ n patterns copied κ visitQ ζ K (fun _ _ _ _ => 1)
      giantTwoSidedExpandedIndependentFourierMoment patterns
        (fun i p => giantSignedJoinedPattern (S := GiantCandidatePerformedSmall groups) (copied i p)) κ q ζ
        (fun i p => giantSignedJoinedCoefficient (PS := PS) (K i p)) (θ : AddCircle (1 : ℝ)) =
        ((∏ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeBaseline visitQ p.val : ℝ) : ℂ)*
          giantSignedGuardedTraceBoundaryPairing (PS := PS) (k := k) (ell := ell) ν rows
            (giantSignedTraceBirthDistinctIndicator (PS := PS) (k := k) (ell := ell) ν V q ρ θ
              n patterns copied κ visitQ ζ K (fun _ _ _ _ => 1))) :
    ∃ Eid : ℝ, 0 < Eid ∧ ∃ m J₀ : ℕ, 1 ≤ m ∧ idealSourceDimensionThreshold m ell ≤ J₀ ∧
      ∀ J : ℕ, J₀ ≤ J →
      ∀ᶠ x : ℝ in atTop,
        let L := Real.log x
        ∀ groups ∈ giantCandidateRetainedOutcomes x threshold,
        let B := GiantCandidatePerformedBig groups
        let PB := giantCandidatePerformedBigBand groups
        let P := fun g : ↥groups => giantCandidateGroup x g.val
        ∃ (B₁ B₂ : Finset B) (hmJ : m ≤ J), Disjoint B₁ B₂ ∧ B₁ ∪ B₂ = Finset.univ ∧
          let family := idealResidualPatterns (idealSourceProbes B₁ hmJ) (idealSourceProbes B₂ hmJ)
          let vmin := Real.log 2/2
          let C₀ := giantCandidateGroupLogRate
          let d := (45/100 : ℝ)
          let Q := ⌊L^(idealSourceRationalExponent (Eid+1) C₀ vmin d m)⌋₊
          let h := L^(-idealSourceWidthExponent (Eid+1) C₀ vmin d C m)
          let ξ := L^(-idealSourceThresholdExponent (Eid+1) C₀ vmin d C m)
          let W := 1 + ((Q : ℝ)^2 / ξ)^2
          (∀ p ∈ family, ∀ g, (idealResidualCopied p g).card ≤ m) ∧
          (family.card : ℝ)*W ≤ L^(idealSourceCostExponent (Eid+1) C₀ vmin d C m) ∧
          let copied (p : IdealResidualPattern B J) := giantCandidatePerformedPattern groups (idealResidualCopied p)
          let K (p : IdealResidualPattern B J) : GiantTwoSidedPatternCoefficient P (copied p) ell :=
            giantCandidatePerformedCoefficient groups (idealResidualCoefficient PB Q h ξ p)
          ∀ (step : ℤ), step ≠ 0 → (step.natAbs : ℝ) ≤ L^Cstep →
          ∀ (ζ : ℝ), |ζ| ≤ L^C →
          ∀ X : ℝ, x^τ ≤ X → X ≤ x^(1/τ) →
          let roots := giantTwoSidedRootInterval X
          let Z := giantTwoSidedRootSlice X
          ∀ u v : ℕ → ℂ, (∀ r ∈ roots, ‖u r‖ ≤ 1) → (∀ r ∈ Z, ‖v r‖ ≤ 1) →
          let F (r : ℕ) := if r ∈ roots then u r * conj (giantCandidateFirstEndpoint e ε x r) else 0
          let G (r : ℕ) := v r * (χ r * giantCandidateAllocationCore (giantCandidateFullPrimes x)
            (Finset.univ.biUnion P) (Real.exp (L^(6/25 : ℝ))) (x^γ) j r)
          let damp (r : ℕ) := (giantTwoSidedEndpointDamping P (J+ell) q r : ℂ)
          ‖giantTwoSidedPhysicalWeightedPairing
            (giantTwoSidedPhysicalFamilyMatrix (Z := Z) family copied step q ζ K)
            (fun s => damp s.val.1.val*F s.val.1.val) (fun s => damp s.val.1.val*G s.val.1.val)‖ ≤
              8*X*L^(-(E+1)+((j*j:ℕ):ℝ)+2) := by
  obtain ⟨Eid,hEid,m,J₀,hm,hThreshold,hselect⟩ :=
    giantCandidatePerformedSourceMoment_of_memory_identity_at_rate threshold C Cstep E τ hthreshold ell
      hq hq1 hρ hρ1 hqρ hC hE hτ hell hIdentity
  refine ⟨Eid,hEid,m,J₀,hm,hThreshold,?_⟩
  intro J hJ
  filter_upwards [hselect J hJ, giantCandidatePhysicalEndpointPairing_eventually_of_moment.{0}
    e he hε hεq χ hγ hτ ⟨hq.le,hq1.le⟩ j J ell hj Cstep (E+1)] with x hselect hpair
  intro L groups hgroups B PB P
  obtain ⟨hsmall,hbig⟩ := (giantCandidatePerformed_retained_iff groups).mp hgroups
  obtain ⟨B₁,B₂,hmJ,hdis,hunion,hcap,hcost,hM⟩ := hselect groups hsmall hbig
  refine ⟨B₁,B₂,hmJ,hdis,hunion,hcap,hcost,?_⟩
  intro copied K step hstep0 hstep ζ hζ X hX hXhi roots Z u v hu hv F G damp
  let n := giantTwoSidedSourceMomentLength x
  let I := IdealResidualPattern B J
  let family := idealResidualPatterns (idealSourceProbes B₁ hmJ) (idealSourceProbes B₂ hmJ)
  let C₀ := giantCandidateGroupLogRate
  let vmin := Real.log 2/2
  let d := (45/100 : ℝ)
  let Q := ⌊L^(idealSourceRationalExponent (Eid+1) C₀ vmin d m)⌋₊
  let h := L^(-idealSourceWidthExponent (Eid+1) C₀ vmin d C m)
  let ξ := L^(-idealSourceThresholdExponent (Eid+1) C₀ vmin d C m)
  let Kbig (p : I) : GiantTwoSidedPatternCoefficient PB (idealResidualCopied p) ell :=
    idealResidualCoefficient PB Q h ξ p
  let reverse (i : Fin n) : Bool := decide (i.val%2 ≠ 0)
  let sign (i : Fin n) := if reverse i then -step.sign else step.sign
  have hsign (i : Fin n) : sign i = 1 ∨ sign i = -1 :=
    giantTwoSidedSourceAlternating_sign hstep0 (reverse i)
  have hnorm := hM step.natAbs (Int.natAbs_pos.mpr hstep0) hstep (fun _ => ζ) (fun _ => hζ)
    reverse sign hsign X hX
  refine hpair groups I family copied step hstep ζ K X hX hXhi ?_ u v hu hv
  rw [giantCandidatePerformedAlternatingMoment_eq_source (n := n) groups family idealResidualCopied step q ζ Kbig roots Z]
  exact hnorm

end
end ArtinMatthews
