module

public import ArtinMatthews.GiantSignedSourceCappedResidualWord
public import ArtinMatthews.GiantSignedSourceActualHighRank
public import ArtinMatthews.GiantSignedSourceDistinctRankJoin


set_option backward.privateInPublic true
@[expose] public section

/-! The common residual family gives the unrestricted original
signed boundary with its global distinct-birth guard. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
universe u

theorem giantSignedSourceDistinctResidualWord_eventually
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
      E+2 + giantSignedSourceVisitExponent C₀ vmax ρ v + 3 < G ∧
      0 ≤ Cs ∧ G+Cs+2 < Eid ∧
      ∃ m : ℕ, 1 ≤ m ∧ ∃ Ca : ℝ, 0 ≤ Ca ∧
      ∃ J₀ : ℕ, idealSourceDimensionThreshold m ell ≤ J₀ ∧
      ∀ J : ℕ, J₀ ≤ J →
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
                  n patterns copied κ visitQ ζ' K (fun _ _ _ _ => 1)‖ ≤ (L ^ (-(E+2))) ^ n ∧
                ‖giantSignedDoubledChronologicalBoundaryPairing ν V q ρ θ
                  n patterns copied κ visitQ ζ' K η‖ /
                  (2 : ℝ) ^ (R - (ell+m)*Fintype.card B*n) ≤ (L ^ (-(E+2))) ^ n ∧
                let rows := giantSignedChronologicalTraceRows (PS := PS) ν V q ρ θ n patterns copied
                  κ visitQ ζ' K (fun _ _ _ _ => 1)
                let distinct := giantSignedTraceBirthDistinctIndicator (PS := PS) ν V q ρ θ n
                  patterns copied κ visitQ ζ' K (fun _ _ _ _ => 1)
                ‖giantSignedGuardedTraceBoundaryPairing ν rows distinct‖ ≤ (L ^ (-(E+1))) ^ n ∧
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
  have hE' : 0 ≤ E+2 := by linarith
  obtain ⟨v,G,Cs,Eid,hv,hweights,hG,hCs,hEid,m,hm,Ca,hCa,J₀,hJ₀,hfamily⟩ :=
    giantSignedSourceCappedResidualWord_eventually.{u} c₀ C₀ vmin vmax b c d C Cstep (E+2) ell
      hq hq1 hρ hρ1 hqρ hc₀ hC₀ hvmin hvmax hc hbc hd hC hE' hell
  obtain ⟨BS,hBS,hsmallrow⟩ := giantSignedSmallRowBudget_exists hq hq1 hvmin ell
  have hCv : 0 ≤ giantSignedSourceVisitExponent C₀ vmax ρ v := by
    unfold giantSignedSourceVisitExponent
    positivity
  have hEid0 : 0 ≤ Eid+1 := by linarith
  let C₁ := idealSourceCostExponent (Eid+1) C₀ vmin d C m
  have hC₁ : 0 ≤ C₁ :=
    (idealSourceParameters_nonnegative (v₀ := vmin) hEid0 hC₀ hd hC m).2.2.2.2
  let Ch := giantSignedSourceHighRankCostExponent C₀ C₁ BS ρ v vmin vmax (ell+m)
  have hCh : 0 ≤ Ch := giantSignedSourceHighRankCostExponent_nonneg (ell+m) hC₀ hC₁ hvmax hρ
    (zero_le_one.trans hv.le)
  let scale := 2*(2*Ch+(E+2)+1)
  have hscale : 0 ≤ scale := by unfold scale; positivity
  have hrow (n : ℕ) (i : Fin (n+1)) : |giantSignedSourceVisitQ q n i/ρ^2| +
      |-(1-giantSignedSourceVisitQ q n i)/ρ|/v ≤ 1 := (hweights n i 0 le_rfl hvmax).1.le
  refine ⟨v,G,Cs,Eid,hv,hweights,hG,hCs,hEid,m,hm,Ca,hCa,J₀,hJ₀,?_⟩
  intro J hJ
  have hM : 1 ≤ J+ell := hell.trans (Nat.le_add_left _ _)
  filter_upwards [hfamily scale hscale J hJ,
    giantSignedSourceCappedBirth_high_rank_sum_eventually (E := E+2) (scale := scale)
      J ell m hM hq hq1.le hρ hρ1 hC₀ hvmin hvmax hv.le hc hC₁ hBS hsmallrow hrow le_rfl,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (3 : ℝ)),
    giantSignedSourceMomentLength_tendsto.eventually (eventually_ge_atTop (1 : ℝ))]
    with x hselect hhigh hL hnReal
  dsimp only
  intro B _ _ PB _ hPB hdisB hVmin hVmax hinterval hband hBlo hBhi
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  have hn : 1 ≤ n := by exact_mod_cast hnReal
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
  have hp (g : B) (p : PB g) : Real.exp (L^c) ≤ (p.val : ℝ) :=
    (hband g p.val p.property).1
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hL0 : 0 < L := by change 3 ≤ L at hL; linarith
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hL0 _
  have hK (i : Fin n) (p : IdealResidualPattern B J) (_ : p ∈ patterns i)
      (a b : MarkedPhysicalMarking PB (J+ell))
      (aux : GiantTwoSidedPatternAuxiliary PB (copied i p)) : ‖K i p a b aux‖ ≤ W :=
    giantSignedOrientedCoefficient_norm (reverse i) (idealResidualCoefficient PB Q h ξ p)
      (idealResidualCoefficient_norm PB Q h hξ p) a b aux
  obtain ⟨hword,hdouble,hcapErr,hlow,hedge⟩ :=
    hblock S PS hPS hdisS hsep hVsmall hsmall hSlo hShi kStep hk hkpow θ ζ hζ reverse sign hsign
  have hhigh' := hhigh S B (IdealResidualPattern B J) PS PB hPS hPB hdisS hVsmall hVmin hVmax
    hp hShi hBhi W hW θ patterns copied (fun _ => hcap) (fun _ => hcost) κ ζ' K hK
  refine ⟨hword,hdouble,?_,hedge⟩
  exact giantSignedBirthDistinctBoundary_norm_of_rank_bounds (PS := PS) R ν V q ρ θ
    n patterns copied κ visitQ ζ' K (giantSignedSourceRankCutoff c scale x) hL hn hcapErr hlow hhigh'

end
end ArtinMatthews
