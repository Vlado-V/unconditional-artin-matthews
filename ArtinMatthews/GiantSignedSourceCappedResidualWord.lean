module

public import ArtinMatthews.GiantSignedSourceProjectedResidualWord
public import ArtinMatthews.GiantSignedSourceActualLowRank
public import ArtinMatthews.GiantSignedCappedBoundaryRank


set_option backward.privateInPublic true
@[expose] public section

/-! The common residual family controls the low-rank capped birth sum
and the true distinct-birth error from imposing the memory cap. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
universe u

local instance sourceCappedResidualPermutationFintype {B : Type*} [Fintype B] {M n H : ℕ} :
    Fintype (Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) :=
  @Equiv.instFintype (GiantSignedUniformBirthAddress B M n H)
    (GiantSignedUniformBirthAddress B M n H) inferInstance inferInstance inferInstance inferInstance

theorem giantSignedSourceCappedResidualWord_eventually
    (c₀ C₀ vmin vmax b c d C Cstep E : ℝ) (ell : ℕ)
    {q ρ : ℝ} (hq : 0 < q) (hq1 : q < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hqρ : Real.sqrt q < ρ ^ 2) (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀)
    (hvmin : 0 < vmin) (hvmax : 0 ≤ vmax) (hc : 0 < c) (hbc : b < c)
    (hd : 0 ≤ d) (hC : 0 ≤ C) (hE : 0 ≤ E) (hell : 1 ≤ ell) :
    ∃ v G Cs Eid : ℝ, 1 < v ∧
      (∀ (n : ℕ) (i : Fin (n+1)) (Vg : ℝ), 0 ≤ Vg → Vg ≤ vmax →
        |giantSignedSourceVisitQ q n i / ρ ^ 2| +
          |-(1-giantSignedSourceVisitQ q n i) / ρ| / v < 1 ∧
        |giantSignedSourceVisitQ q n i / ρ ^ 2| +
          2 * |-(1-giantSignedSourceVisitQ q n i) * Vg / ρ| / v < 1) ∧
      E + giantSignedSourceVisitExponent C₀ vmax ρ v + 3 < G ∧
      0 ≤ Cs ∧ G+Cs+2 < Eid ∧
      ∃ m : ℕ, 1 ≤ m ∧ ∃ Ca : ℝ, 0 ≤ Ca ∧
      ∃ J₀ : ℕ, idealSourceDimensionThreshold m ell ≤ J₀ ∧
      ∀ scale : ℝ, 0 ≤ scale → ∀ J : ℕ, J₀ ≤ J →
        ∀ᶠ x : ℝ in atTop,
          let L := Real.log x
          let n := giantTwoSidedSourceMomentLength x
          ∀ (B : Type u) [Fintype B] [DecidableEq B] (PB : B → Finset ℕ)
            [∀ g, ∀ p : PB g, NeZero p.val],
            (∀ j p, p ∈ PB j → p.Prime) → Pairwise (fun i j => Disjoint (PB i) (PB j)) →
            (∀ j, vmin ≤ bandReciprocalMass (PB j)) →
            (∀ j, bandReciprocalMass (PB j) ≤ vmax) → (∀ j, IdealPrimeInterval (PB j)) →
            (∀ j p, p ∈ PB j → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
            c₀ * Real.log L ≤ (Fintype.card B : ℝ) → (Fintype.card B : ℝ) ≤ C₀ * Real.log L →
            ∃ (B₁ B₂ : Finset B) (hmJ : m ≤ J), Disjoint B₁ B₂ ∧ B₁ ∪ B₂ = Finset.univ ∧
              let family := idealResidualPatterns (idealSourceProbes B₁ hmJ) (idealSourceProbes B₂ hmJ)
              let Q := ⌊L^(idealSourceRationalExponent (Eid+1) C₀ vmin d m)⌋₊
              let h := L^(-idealSourceWidthExponent (Eid+1) C₀ vmin d C m)
              let ξ := L^(-idealSourceThresholdExponent (Eid+1) C₀ vmin d C m)
              let W := 1 + ((Q : ℝ)^2 / ξ)^2
              (∀ p ∈ family, ∀ g, (idealResidualCopied p g).card ≤ m) ∧
              (family.card : ℝ) * W ≤ L^(idealSourceCostExponent (Eid+1) C₀ vmin d C m) ∧
              ∀ (S : Type u) [Fintype S] [DecidableEq S] (PS : S → Finset ℕ)
                [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val],
                (∀ j p, p ∈ PS j → p.Prime) → Pairwise (fun i j => Disjoint (PS i) (PS j)) →
                (∀ i j, Disjoint (PS i) (PB j)) → (∀ j, vmin ≤ bandReciprocalMass (PS j)) →
                (∀ j p, p ∈ PS j → (p : ℝ) ≤ Real.exp (L^b)) →
                c₀ * Real.log L ≤ (Fintype.card S : ℝ) →
                (Fintype.card S : ℝ) ≤ C₀ * Real.log L →
                ∀ (kStep : ℕ), 0 < kStep → (kStep : ℝ) ≤ L^Cstep →
                ∀ (θ : ℝ) (ζ : Fin n → ℝ), (∀ i, |ζ i| ≤ L^C) →
                ∀ (reverse : Fin n → Bool) (sign : Fin n → ℤ),
                  (∀ i, sign i = 1 ∨ sign i = -1) →
                let visitQ := giantSignedSourceVisitQ q n
                let ν := fun g => giantSignedTiltedPrimeLaw (PB g) visitQ
                let V := fun g => bandReciprocalMass (PB g)
                let R := giantSignedSourceMemoryLimit L
                let κ := fun i => sign i * (kStep : ℤ)
                let ζ' := fun i => if reverse i then -ζ i else ζ i
                let K (i : Fin n) (p : IdealResidualPattern B J) :=
                  giantSignedOrientedCoefficient (reverse i) (idealResidualCoefficient PB Q h ξ p)
                let patterns : Fin n → Finset (IdealResidualPattern B J) := fun _ => family
                let copied : Fin n → IdealResidualPattern B J → B → Finset (Fin J) :=
                  fun _ => idealResidualCopied
                let η (i : Fin n) (p : IdealResidualPattern B J)
                    (s : GiantSignedState PS PB (J+ell))
                    (r : GiantSignedRawEdgeMove PS PB ell (copied i p) s.2.2) :=
                  giantSignedRawEdgeAbsoluteMultiplier ν V (κ i) q ρ θ (ζ' i) (K i p)
                    (fun _ _ => 1) s r
                ‖giantSignedProjectedChronologicalBoundaryPairing (PS := PS) R ν V q ρ θ
                  n patterns copied κ visitQ ζ' K (fun _ _ _ _ => 1)‖ ≤ (L ^ (-E)) ^ n ∧
                ‖giantSignedDoubledChronologicalBoundaryPairing ν V q ρ θ
                  n patterns copied κ visitQ ζ' K η‖ /
                  (2 : ℝ) ^ (R - (ell+m)*Fintype.card B*n) ≤ (L ^ (-E)) ^ n ∧
                let rows := giantSignedChronologicalTraceRows (PS := PS) ν V q ρ θ n patterns copied
                  κ visitQ ζ' K (fun _ _ _ _ => 1)
                let distinct := giantSignedTraceBirthDistinctIndicator (PS := PS) ν V q ρ θ n
                  patterns copied κ visitQ ζ' K (fun _ _ _ _ => 1)
                ‖giantSignedGuardedTraceBoundaryPairing ν rows distinct -
                  giantSignedGuardedTraceBoundaryPairing ν rows (fun s t =>
                    if GiantSignedTraceWithin (fun z => (∑ g, z.2.2.1 g) ≤ R) rows s t then
                      distinct s t else 0)‖ ≤ (L ^ (-E)) ^ n ∧
                (∑ σ : Equiv.Perm (GiantSignedUniformBirthAddress B (J+ell) n R),
                  if giantSignedUniformBirthRank σ < giantSignedSourceRankCutoff c scale x then
                    ‖giantSignedCappedBirthEventBoundary (PS := PS) R ν V q ρ θ n patterns copied
                      κ visitQ ζ' K (fun _ _ _ _ => 1) σ‖ else 0) ≤ (L ^ (-E)) ^ n ∧
                ∀ (i : Fin n) (f : GiantSignedState PS PB (J+ell) → ℂ),
                  (∀ s a, GiantSignedMemorySymmetric (fun mem => f (s,a,mem))) →
                  (giantSignedStateEnergy PS ν
                    (giantSignedProjectedRawEdgeFamilyApply R ν V family idealResidualCopied
                      (κ i) q ρ θ (ζ' i) (K i) (fun _ _ _ => 1) f) ≤
                    ENNReal.ofReal ((L^(-G))^2) * giantSignedStateEnergy PS ν f) ∧
                  (∀ (φ : (p : IdealResidualPattern B J) →
                    (s : GiantSignedState PS PB (J+ell)) →
                    GiantSignedRawEdgeMove PS PB ell (idealResidualCopied p) s.2.2 → ℂ),
                    (∀ p ∈ family, ∀ s r, ‖φ p s r‖ ≤ 1) →
                    giantSignedStateEnergy PS ν
                      (giantSignedProjectedRawEdgeFamilyApply R ν V family idealResidualCopied
                        (κ i) q ρ θ (ζ' i) (K i) φ f) ≤
                      ENNReal.ofReal (L^(2*Ca)) * giantSignedStateEnergy PS ν f) := by
  obtain ⟨v,G,Cs,Eid,hv,hweights,hG,hCs,hEid,m,hm,Ca,hCa,J₀,hJ₀,hfamily⟩ :=
    giantSignedSourceProjectedResidualWord_eventually.{u} c₀ C₀ vmin vmax b c d C Cstep E ell
      hq hq1 hρ hρ1 hqρ hc₀ hC₀ hvmin hvmax hc hbc hd hC hE hell
  obtain ⟨BS,hBS,hsmallrow⟩ := giantSignedSmallRowBudget_exists hq hq1 hvmin ell
  refine ⟨v,G,Cs,Eid,hv,hweights,hG,hCs,hEid,m,hm,Ca,hCa,J₀,hJ₀,?_⟩
  intro scale hscale J hJ
  have hM : 1 ≤ J+ell := hell.trans (Nat.le_add_left _ _)
  filter_upwards [hfamily J hJ,
    giantSignedSourceCappedBirth_low_rank_sum_eventually J ell m hM hq hq1 hρ hρ1
      hC₀ hvmin hvmax (zero_lt_one.trans hv) hCa hE hc hscale hG hweights,
    giantSignedSourceTiltedBoundary_budget_eventually q c C₀ J ell hM hq.le hq1.le hc hC₀,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with x hselect hlow htilt hL
  dsimp only
  intro B _ _ PB _ hPB hdisB hVmin hVmax hinterval hband hBlo hBhi
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  obtain ⟨B₁,B₂,hmJ,hdis,hunion,hcap,hcost,hblock⟩ :=
    hselect B PB hPB hdisB hVmin hVmax hinterval hband hBlo hBhi
  refine ⟨B₁,B₂,hmJ,hdis,hunion,hcap,hcost,?_⟩
  try dsimp only
  intro S _ _ PS _ hPS hdisS hsep hVsmall hsmall hSlo hShi kStep hk hkpow θ ζ hζ reverse sign hsign
  let family := idealResidualPatterns (idealSourceProbes B₁ hmJ) (idealSourceProbes B₂ hmJ)
  let Q := ⌊L^(idealSourceRationalExponent (Eid+1) C₀ vmin d m)⌋₊
  let h := L^(-idealSourceWidthExponent (Eid+1) C₀ vmin d C m)
  let ξ := L^(-idealSourceThresholdExponent (Eid+1) C₀ vmin d C m)
  let W := 1 + ((Q : ℝ)^2 / ξ)^2
  let patterns : Fin n → Finset (IdealResidualPattern B J) := fun _ => family
  let copied : Fin n → IdealResidualPattern B J → B → Finset (Fin J) :=
    fun _ => idealResidualCopied
  let visitQ := giantSignedSourceVisitQ q n
  let ν := fun g => giantSignedTiltedPrimeLaw (PB g) visitQ
  let V := fun g => bandReciprocalMass (PB g)
  let R := giantSignedSourceMemoryLimit L
  let κ := fun (i : Fin n) => sign i * (kStep : ℤ)
  let ζ' := fun (i : Fin n) => if reverse i then -ζ i else ζ i
  let K (i : Fin n) (p : IdealResidualPattern B J) :
      GiantTwoSidedPatternCoefficient PB (idealResidualCopied p) ell :=
    giantSignedOrientedCoefficient (reverse i) (idealResidualCoefficient PB Q h ξ p)
  have hVS (j : S) : 0 < bandReciprocalMass (PS j) := hvmin.trans_le (hVsmall j)
  have hVB (g : B) : 0 < V g := hvmin.trans_le (hVmin g)
  have hp (g : B) (p : PB g) : Real.exp (L^c) ≤ (p.val : ℝ) :=
    (hband g p.val p.property).1
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hL _
  have hK (i : Fin n) (p : IdealResidualPattern B J) (_ : p ∈ patterns i)
      (a b : MarkedPhysicalMarking PB (J+ell))
      (aux : GiantTwoSidedPatternAuxiliary PB (copied i p)) : ‖K i p a b aux‖ ≤ W :=
    giantSignedOrientedCoefficient_norm (reverse i) (idealResidualCoefficient PB Q h ξ p)
      (idealResidualCoefficient_norm PB Q h hξ p) a b aux
  obtain ⟨hword,hdouble,hedge⟩ :=
    hblock S PS hPS hdisS hsep hVsmall hsmall hSlo hShi kStep hk hkpow θ ζ hζ reverse sign hsign
  obtain ⟨hν,hMass,_⟩ := htilt S B PS PB hPS hdisS hVS hVB hp hBhi
  refine ⟨hword,hdouble,?_,?_,hedge⟩
  · exact (giantSignedGuardedTraceBoundary_projection_error hPS hPB hdisS hVS hVB ν hν V
      hvmin hVmin hMass hq hq1.le hBS (fun j z => hsmallrow _ (hVsmall j) z)
      hρ.le hρ1 hW m R θ n patterns copied (fun _ => hcap) κ visitQ ζ' K hK
      (fun _ _ _ _ => 1) (fun _ _ _ _ _ => norm_one.le)
      (giantSignedTraceBirthDistinctIndicator ν V q ρ θ n patterns copied κ visitQ ζ' K
        (fun _ _ _ _ => 1))
      (giantSignedTraceBirthDistinctIndicator_norm_le ν V q ρ θ n patterns copied κ visitQ ζ' K
        (fun _ _ _ _ => 1))).trans hdouble
  · exact hlow S B (IdealResidualPattern B J) PS PB hPS hPB hdisS hVsmall hVmin hVmax hp hBhi
      W hW θ patterns copied (fun _ => hcap) κ ζ' K hK
      (fun i f hf => (hedge i f hf).1) (fun i f hf => (hedge i f hf).2)

end
end ArtinMatthews
