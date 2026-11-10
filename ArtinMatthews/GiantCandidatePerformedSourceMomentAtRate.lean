module

public import ArtinMatthews.GiantSignedCanonicalCleanSuccessors
public import ArtinMatthews.GiantSignedCappedBoundaryRank
public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantTwoSidedExpandedFourier
public import ArtinMatthews.GiantCandidatePerformedGeometry
public import ArtinMatthews.GiantCandidatePerformedPhysicalBudget
public import ArtinMatthews.GiantCandidatePerformedReturnJoin
public import ArtinMatthews.GiantSignedSourceDistinctResidualWord
public import ArtinMatthews.GiantSignedSourceReturnScalars
public import ArtinMatthews.GiantTwoSidedPatternRunActual
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal selected physical moment uses the same residual family
as the signed memory boundary at any fixed positive retained-group rate.
The finite memory identity connects the two representations. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem giantCandidatePerformedSourceMoment_of_memory_identity_at_rate
    (c₀ C Cstep E γ : ℝ) (hc₀ : 0 < c₀) (ell : ℕ) {q ρ : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hqρ : Real.sqrt q < ρ^2) (hC : 0 ≤ C) (hE : 0 ≤ E) (hγ : 0 < γ) (hell : 1 ≤ ell)
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
        let n := giantTwoSidedSourceMomentLength x
        ∀ groups : Finset (GiantCandidateGroupIndex x),
          c₀ * Real.log L ≤
            (Fintype.card (GiantCandidatePerformedSmall groups) : ℝ) →
          c₀ * Real.log L ≤
            (Fintype.card (GiantCandidatePerformedBig groups) : ℝ) →
        let B := GiantCandidatePerformedBig groups
        let PB := giantCandidatePerformedBigBand groups
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
          ∀ (kStep : ℕ), 0 < kStep → (kStep : ℝ) ≤ L^Cstep →
          ∀ (ζ : Fin n → ℝ), (∀ i, |ζ i| ≤ L^C) →
          ∀ (reverse : Fin n → Bool) (sign : Fin n → ℤ), (∀ i, sign i = 1 ∨ sign i = -1) →
          let κ := fun i => sign i * (kStep : ℤ)
          let ζ' := fun i => if reverse i then -ζ i else ζ i
          let K (i : Fin n) (p : IdealResidualPattern B J) :
              GiantTwoSidedPatternCoefficient PB (idealResidualCopied p) ell :=
            giantSignedOrientedCoefficient (reverse i) (idealResidualCoefficient PB Q h ξ p)
          ∀ X : ℝ, x^γ ≤ X →
            ‖giantTwoSidedExpandedPhysicalMoment (fun _ => family)
              (fun _ p => giantCandidatePerformedPattern groups (idealResidualCopied p)) κ q ζ'
              (fun i p => giantCandidatePerformedCoefficient groups (K i p))
              (giantTwoSidedRootInterval X) (giantTwoSidedRootSlice X)‖ /
              ((⌈2*X⌉₊-⌈X⌉₊ : ℕ) : ℝ) ≤ (L^(-(E+1)))^n := by
  let C₀ := giantCandidateGroupLogRate
  let vmin := Real.log 2/2
  let d := (45/100 : ℝ)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC₀ : 0 ≤ C₀ := by unfold C₀ giantCandidateGroupLogRate; positivity
  have hvmin : 0 < vmin := half_pos hlog2
  have hE' : 0 ≤ E+1 := by linarith
  obtain ⟨v,G,Cs,Eid,hv,hweights,hG,hCs,hEid,m,hm,Ca,hCa,J₀,hJ₀,hword⟩ :=
    giantSignedSourceDistinctResidualWord_eventually.{0} c₀ C₀ vmin 1 (35/100) (40/100) d C Cstep (E+1) ell
      hq hq1 hρ hρ1 hqρ hc₀ hC₀ hvmin zero_le_one (by norm_num) (by norm_num)
      (by unfold d; norm_num) hC hE' hell
  have hCv : 0 ≤ giantSignedSourceVisitExponent C₀ 1 ρ v := by
    unfold giantSignedSourceVisitExponent
    positivity
  have hEid0 : 0 < Eid := by linarith
  let C₁ := idealSourceCostExponent (Eid+1) C₀ vmin d C m
  refine ⟨Eid,hEid0,m,J₀,hm,hJ₀,?_⟩
  intro J hJ
  have hM : 1 ≤ J+ell := hell.trans (Nat.le_add_left _ _)
  filter_upwards [hword J hJ, giantCandidatePerformedGeometry_eventually,
    giantCandidateSelectedGroups_geometry_eventually,
    giantSignedSourceBigBaseline_eventually (q := q) (c := 40/100) J ell hM hq.le hq1.le
      (by norm_num) hC₀ hvmin,
    giantCandidatePerformedPhysical_norm_eventually_of_independent.{0} J ell m C₁ Cstep (E+1) hE' hq hq1 hγ,
    giantCandidatePattern_step_size_eventually Cstep,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hxword hxgeo hxdis hxbase hxphysical hxsize hL
  dsimp only
  intro groups hSlo hBlo
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  let S := GiantCandidatePerformedSmall groups
  let B := GiantCandidatePerformedBig groups
  let PS := giantCandidatePerformedSmallBand groups
  let PB := giantCandidatePerformedBigBand groups
  let P := fun j : ↥groups => giantCandidateGroup x j.val
  obtain ⟨hPS,hPB,hdisS,hdisB,hsep,hVsmall,hVmin,hVmax,hinterval,hsmall,hbig,hShi,hBhi⟩ := hxgeo groups
  have hP (j : ↥groups) (p : ℕ) (hp : p ∈ P j) : p.Prime := by
    rcases j with ⟨j | j,hj⟩
    · exact hPS ⟨j,hj⟩ p hp
    · exact hPB ⟨j,hj⟩ p hp
  have hJoin (j : S ⊕ B) (p : ℕ) (hp : p ∈ Sum.elim PS PB j) : p.Prime := by
    cases j with
    | inl j => exact hPS j p hp
    | inr j => exact hPB j p hp
  have nzUnion {G : Type} [Fintype G] {bands : G → Finset ℕ}
      (hprime : ∀ j p, p ∈ bands j → p.Prime)
      (p : ↥(markedPhysicalBandPrimes bands)) : NeZero p.val := by
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp p.property
    exact ⟨(hprime j p.val hj).ne_zero⟩
  let nz : ∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val :=
    nzUnion hP
  letI : ∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val := nz
  letI : ∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val :=
    nzUnion hPS
  letI : ∀ p : ↥(markedPhysicalBandPrimes PB), NeZero p.val :=
    nzUnion hPB
  letI : ∀ p : ↥(markedPhysicalBandPrimes (Sum.elim PS PB)), NeZero p.val :=
    nzUnion hJoin
  letI : ∀ g, ∀ p : PB g, NeZero p.val := fun g p => ⟨(hPB g p.val p.property).ne_zero⟩
  have hp (g : B) (p : PB g) : Real.exp (L^(40/100 : ℝ)) ≤ (p.val : ℝ) := (hbig g p.val p.property).1
  obtain ⟨hbase,hbase0,hbase1⟩ := hxbase B PB hVmin hp hBhi
  obtain ⟨B₁,B₂,hmJ,hdis,hunion,hcap,hcost,hblock⟩ :=
    hxword B PB hPB hdisB hVmin hVmax hinterval hbig hBlo hBhi
  refine ⟨B₁,B₂,hmJ,hdis,hunion,hcap,hcost,?_⟩
  try dsimp only
  intro kStep hk hkpow ζ hζ reverse sign hsign X hX
  let family := idealResidualPatterns (idealSourceProbes B₁ hmJ) (idealSourceProbes B₂ hmJ)
  let Q := ⌊L^(idealSourceRationalExponent (Eid+1) C₀ vmin d m)⌋₊
  let h := L^(-idealSourceWidthExponent (Eid+1) C₀ vmin d C m)
  let ξ := L^(-idealSourceThresholdExponent (Eid+1) C₀ vmin d C m)
  let W := 1 + ((Q : ℝ)^2 / ξ)^2
  let I := IdealResidualPattern B J
  let patterns : Fin n → Finset I := fun _ => family
  let copied : Fin n → I → B → Finset (Fin J) := fun _ => idealResidualCopied
  let κ := fun (i : Fin n) => sign i * (kStep : ℤ)
  let ζ' := fun (i : Fin n) => if reverse i then -ζ i else ζ i
  let K (i : Fin n) (p : I) : GiantTwoSidedPatternCoefficient PB (idealResidualCopied p) ell :=
    giantSignedOrientedCoefficient (reverse i) (idealResidualCoefficient PB Q h ξ p)
  have hstep (i : Fin n) : ((κ i).natAbs : ℝ) ≤ L^Cstep := by
    rcases hsign i with hs | hs <;> simpa [κ,hs] using hkpow
  have hstep0 (i : Fin n) : 0 < (κ i).natAbs := by
    rcases hsign i with hs | hs <;> simpa [κ,hs] using hk
  have hsize (i : Fin n) (g : S ⊕ B) (p : ℕ) (hp : p ∈ Sum.elim PS PB g) :
      (κ i).natAbs < p := by
    cases g with
    | inl g => exact hxsize (κ i) (hstep i) p (mem_giantCandidateFullPrimes.mpr ⟨.inl g.val,hp⟩)
    | inr g => exact hxsize (κ i) (hstep i) p (mem_giantCandidateFullPrimes.mpr ⟨.inr g.val,hp⟩)
  have hW : 0 ≤ W := by unfold W; positivity
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hL _
  have hK (i : Fin n) (p : I) (_ : p ∈ patterns i)
      (a b : MarkedPhysicalMarking PB (J+ell))
      (aux : GiantTwoSidedPatternAuxiliary PB (copied i p)) : ‖K i p a b aux‖ ≤ W :=
    giantSignedOrientedCoefficient_norm (reverse i) (idealResidualCoefficient PB Q h ξ p)
      (idealResidualCoefficient_norm PB Q h hξ p) a b aux
  have hindep := giantCandidatePerformedIndependentMoment_norm_of_trace groups (hxdis groups).1
    patterns copied κ q ρ ζ' K hbase0 hbase1
    (hIdentity groups hPS hPB hdisS hdisB hsep (fun j => hvmin.trans_le (hVsmall j))
      (fun j => hvmin.trans_le (hVmin j)) I (giantTwoSidedSourceMomentLength_pos hL).ne'
      hbase patterns copied κ hstep0 hsize ζ' K)
    (fun θ => (hblock S PS hPS hdisS hsep hVsmall hsmall hSlo hShi kStep hk hkpow θ ζ hζ reverse sign hsign).2.2.1)
  exact hxphysical groups nz I patterns copied (fun _ => hcap) κ hstep ζ' K W hW hK (fun _ => hcost) hindep X hX

end
end ArtinMatthews
