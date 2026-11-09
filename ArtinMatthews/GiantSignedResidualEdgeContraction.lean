module

public import ArtinMatthews.GiantSignedCanonicalCleanSuccessors
public import ArtinMatthews.GiantSignedProjectedDirtyFamilyRare
public import ArtinMatthews.GiantSignedProjectedEdgeSplitEnergy
public import ArtinMatthews.GiantSignedProjectedRawEnergy
public import ArtinMatthews.GiantSignedSourceSmallConditioning
public import ArtinMatthews.GiantSignedSourceOmissionGain
public import ArtinMatthews.GiantSignedSourceContractionBudget
public import ArtinMatthews.GiantSignedSmallOmissionSize
public import ArtinMatthews.GiantSignedTiltedMass


set_option backward.privateInPublic true
@[expose] public section

/-! The literal source edge uses the same fixed residual family in both
orientations. Its signed norm is small after the actual quadratic memory
projection, and its absolute bound remains available for modified moves. -/
namespace ArtinMatthews
open Filter Finset Set
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

theorem giantSignedSmallStatePrefixProduct_eq_markingProduct
    {S : Type*} [Fintype S] {PS : S → Finset ℕ} {k ell : ℕ}
    (s : GiantTwoSidedResidueState PS (k+ell)) :
    giantSignedSmallPrefixProduct s =
      markedPhysicalMarkingProduct (P:=PS) (M:=k)
        (fun j i => s.val.2 j (Fin.castAdd ell i)) := rfl

theorem giantSignedProjectedResidualEdge_contraction
    (c₀ C₀ vmin vmax b c d C Cstep E N : ℝ) (ell : ℕ)
    {q ρ : ℝ} (hq : 0 < q) (hq1 : q < 1) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hvmin : 0 < vmin) (hc : 0 < c)
    (hbc : b < c) (hd : 0 ≤ d) (hC : 0 ≤ C) (hE : 0 ≤ E) (hell : 1 ≤ ell) :
    ∃ Cs Eid : ℝ, 0 ≤ Cs ∧ E + Cs + 1 ≤ Eid ∧
      ∃ m : ℕ, 1 ≤ m ∧ ∃ Ca : ℝ, 0 ≤ Ca ∧
      ∃ J₀ : ℕ, idealSourceDimensionThreshold m ell ≤ J₀ ∧
      ∀ J : ℕ, J₀ ≤ J →
        ∀ᶠ L : ℝ in atTop, ∀ (B : Type u) [Fintype B] [DecidableEq B]
          (P : B → Finset ℕ) [∀ j, ∀ p : P j, NeZero p.val],
          (∀ j p, p ∈ P j → p.Prime) → Pairwise (fun i j => Disjoint (P i) (P j)) →
          (∀ j, vmin ≤ bandReciprocalMass (P j)) →
          (∀ j, bandReciprocalMass (P j) ≤ vmax) → (∀ j, IdealPrimeInterval (P j)) →
          (∀ j p, p ∈ P j → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
          c₀ * Real.log L ≤ (Fintype.card B : ℝ) → (Fintype.card B : ℝ) ≤ C₀ * Real.log L →
          ∃ (B₁ B₂ : Finset B) (hmJ : m ≤ J), Disjoint B₁ B₂ ∧ B₁ ∪ B₂ = Finset.univ ∧
            let patterns := idealResidualPatterns (idealSourceProbes B₁ hmJ) (idealSourceProbes B₂ hmJ)
            let Q := ⌊L^(idealSourceRationalExponent (Eid+1) C₀ vmin d m)⌋₊
            let h := L^(-idealSourceWidthExponent (Eid+1) C₀ vmin d C m)
            let ξ := L^(-idealSourceThresholdExponent (Eid+1) C₀ vmin d C m)
            (∀ i ∈ patterns, ∀ j, (idealResidualCopied i j).card ≤ m) ∧
            (patterns.card : ℝ) * (1 + ((Q : ℝ)^2 / ξ)^2) ≤
              L^(idealSourceCostExponent (Eid+1) C₀ vmin d C m) ∧
            ∀ (S : Type v) [Fintype S] [DecidableEq S] (PS : S → Finset ℕ)
              [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val],
              (∀ j p, p ∈ PS j → p.Prime) → Pairwise (fun i j => Disjoint (PS i) (PS j)) →
              (∀ i j, Disjoint (PS i) (P j)) → (∀ j, vmin ≤ bandReciprocalMass (PS j)) →
              (∀ j p, p ∈ PS j → (p : ℝ) ≤ Real.exp (L^b)) →
              c₀ * Real.log L ≤ (Fintype.card S : ℝ) → (Fintype.card S : ℝ) ≤ C₀ * Real.log L →
              ∀ (n : ℕ), (n : ℝ) ≤ L^N →
              ∀ (qStage : Fin n → ℝ), (∀ i, 0 ≤ qStage i) → (∀ i, qStage i ≤ 1) →
              ∀ (kStep : ℕ), 0 < kStep → (kStep : ℝ) ≤ L^Cstep →
              ∀ (θ ζ : ℝ), |ζ| ≤ L^C → ∀ (reverse : Bool) (sign : ℤ),
                (sign = 1 ∨ sign = -1) → ∀ (f : GiantSignedState PS P (J+ell) → ℂ),
                (∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) →
              let ν := fun j => giantSignedTiltedPrimeLaw (P j) qStage
              let V := fun j => bandReciprocalMass (P j)
              let κ := sign * (kStep : ℤ)
              let ζ' := if reverse then -ζ else ζ
              let K (i : IdealResidualPattern B J) :=
                giantSignedOrientedCoefficient reverse (idealResidualCoefficient P Q h ξ i)
              let R := giantSignedSourceMemoryLimit L
              (giantSignedStateEnergy PS ν
                (giantSignedProjectedRawEdgeFamilyApply R ν V patterns idealResidualCopied
                  κ q ρ θ ζ' K (fun _ _ _ => 1) f) ≤
                ENNReal.ofReal ((L^(-E))^2) * giantSignedStateEnergy PS ν f) ∧
              (∀ (η : (i : IdealResidualPattern B J) →
                (s : GiantSignedState PS P (J+ell)) →
                GiantSignedRawEdgeMove PS P ell (idealResidualCopied i) s.2.2 → ℂ),
                (∀ i ∈ patterns, ∀ s r, ‖η i s r‖ ≤ 1) →
                giantSignedStateEnergy PS ν
                  (giantSignedProjectedRawEdgeFamilyApply R ν V patterns idealResidualCopied
                    κ q ρ θ ζ' K η f) ≤
                  ENNReal.ofReal (L^(2*Ca)) * giantSignedStateEnergy PS ν f) := by
  obtain ⟨Cs,hCs,hsmall⟩ := giantSignedSourceSmallConditioning_exists.{v} ell hq hq1 hvmin hC₀
  let Eid := E + Cs + 1
  have hEid : 0 ≤ Eid := by dsimp [Eid]; linarith
  obtain ⟨m,hm,hC₁,hclean⟩ := giantSignedProjectedResidualClean_oriented.{u,v}
    c₀ C₀ vmin c d C Eid N ell hc₀ hC₀ hvmin hc hd hC hEid hell
  obtain ⟨BS,hBS,hbudget⟩ := giantSignedSmallRowBudget_exists hq hq1 hvmin ell
  let C₁ := idealSourceCostExponent (Eid+1) C₀ vmin d C m
  let Ca := giantSignedSourceAbsoluteExponent C₀ C₁ BS ρ 1 vmin vmax 2 (ell+m)
  have hCa : 0 ≤ Ca := by
    have h1 : 0 ≤ Real.log (max 1 BS) := Real.log_nonneg (le_max_left _ _)
    have h2 : 0 ≤ Real.log (max 1 (giantSignedEdgeEnergyConstant ρ 1 vmin vmax 2 (ell+m))) :=
      Real.log_nonneg (le_max_left _ _)
    dsimp only [Ca,giantSignedSourceAbsoluteExponent]
    exact add_nonneg (add_nonneg hC₁ (mul_nonneg hC₀ h1))
      (mul_nonneg (div_nonneg hC₀ (by norm_num)) h2)
  obtain ⟨J₁,hgain⟩ := giantSignedSourceOmissionGain.{v} c₀ Ca E hc₀ ell
    (lt_of_lt_of_le Nat.zero_lt_one hell)
  let J₀ := max J₁ (idealSourceDimensionThreshold m ell)
  refine ⟨Cs,Eid,hCs,le_rfl,m,hm,Ca,hCa,J₀,le_max_right _ _,?_⟩
  intro J hJ
  have hJ₁ : J₁ ≤ J := (le_max_left _ _).trans hJ
  have hJ₂ : idealSourceDimensionThreshold m ell ≤ J := (le_max_right _ _).trans hJ
  have hlen := (rpow_mul_exp_neg_rpow_tendsto N hc (by norm_num : (0 : ℝ) < 1)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have hstep := (rpow_mul_exp_neg_rpow_tendsto Cstep hc (by norm_num : (0 : ℝ) < 1)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hclean J hJ₂, giantSignedSmallOmission_budget_eventually C₀ ell hbc,
    hlen, hstep, eventually_ge_atTop (3 : ℝ)] with L hcleanL hgap hlenL hstepL hL
  intro B _ _ P _ hP hdisB hVmin hVmax hinterval hband hBlo hBhi
  obtain ⟨B₁,B₂,hmJ,hdisBlocks,hunion,hcap,hcost,hcleanBlock⟩ :=
    hcleanL B P hP hdisB hVmin hinterval hband hBlo hBhi
  refine ⟨B₁,B₂,hmJ,hdisBlocks,hunion,hcap,hcost,?_⟩
  dsimp only
  intro S _ _ PS _ hPS hdisS hsep hVSmin hlabels hSlo hShi n hn qStage hqStage0 hqStage1
    kStep hk hkpow θ ζ hζ reverse sign hsign f hsym
  let V (j : B) := bandReciprocalMass (P j)
  let ν (j : B) := giantSignedTiltedPrimeLaw (P j) qStage
  let patterns := idealResidualPatterns (idealSourceProbes B₁ hmJ) (idealSourceProbes B₂ hmJ)
  let Q := ⌊L^(idealSourceRationalExponent (Eid+1) C₀ vmin d m)⌋₊
  let h := L^(-idealSourceWidthExponent (Eid+1) C₀ vmin d C m)
  let ξ := L^(-idealSourceThresholdExponent (Eid+1) C₀ vmin d C m)
  let K (i : IdealResidualPattern B J) : GiantTwoSidedPatternCoefficient P (idealResidualCopied i) ell :=
    giantSignedOrientedCoefficient reverse (idealResidualCoefficient P Q h ξ i)
  let W := 1 + ((Q : ℝ)^2 / ξ)^2
  let κ := sign * (kStep : ℤ)
  let ζ' := if reverse then -ζ else ζ
  let R := giantSignedSourceMemoryLimit L
  let Pmin := Real.exp (L^c)
  let Eabs := giantSignedRawEdgeEnergyConstant ((patterns.card : ℝ)*W) BS
    (Fintype.card S) (Fintype.card B) ρ 1 vmin vmax 2 (ell+m)
  let ε : ℝ := (R : ℝ) / (giantSignedSmallOmissionNumber S (J+ell) ell : ℝ)
  have hL0 : 0 < L := by linarith
  have hL2 : 2 ≤ L := by linarith
  have hVS (j : S) : 0 < bandReciprocalMass (PS j) := hvmin.trans_le (hVSmin j)
  have hVB (j : B) : 0 < V j := hvmin.trans_le (hVmin j)
  have hPmin : 0 < Pmin := Real.exp_pos _
  have hN : (n : ℝ)/Pmin ≤ 1/2 := by
    have hN' : L^N / Pmin < 1/2 := by
      simpa only [Pmin, Set.mem_Iio, neg_one_mul, Real.exp_neg, div_eq_mul_inv] using hlenL
    exact (div_le_div_of_nonneg_right hn hPmin.le).trans hN'.le
  have hnP : (n : ℝ) < Pmin := (div_lt_one hPmin).mp (hN.trans_lt (by norm_num))
  have hPbound (j : B) (p : P j) : Pmin ≤ (p.val : ℝ) := (hband j p.val p.property).1
  have hν (j : B) (p : P j) : 0 ≤ ν j p :=
    (giantSignedTiltedPrimeLaw_pos (P j) qStage (hVB j) hqStage0
      (fun p' => by exact_mod_cast hnP.trans_le (hPbound j p')) p).le
  have hmass (j : B) : (∑ p : P j, ν j p) ≤ 2 :=
    giantSignedTiltedPrimeLaw_sum_le_two (P j) qStage (hVB j) hqStage0 hqStage1 Pmin hPmin (hPbound j) hN
  have hkP : L^Cstep < Pmin := by
    apply (div_lt_one hPmin).mp
    simpa only [Pmin, Set.mem_Iio, neg_one_mul, Real.exp_neg, div_eq_mul_inv] using hstepL
  have hstepB (j : B) (p : ℕ) (hp : p ∈ P j) : kStep < p := by
    exact_mod_cast hkpow.trans_lt (hkP.trans_le (hband j p hp).1)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hL0 _
  have hK (i : IdealResidualPattern B J) (_hi : i ∈ patterns)
      (a b : MarkedPhysicalMarking P (J+ell))
      (aux : GiantTwoSidedPatternAuxiliary P (idealResidualCopied i)) :
      ‖K i a b aux‖ ≤ W :=
    giantSignedOrientedCoefficient_norm reverse (idealResidualCoefficient P Q h ξ i)
      (idealResidualCoefficient_norm P Q h hξ i) a b aux
  have hSmallBudget (j : S) (z : ℕ) :
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ)/2) ≤ BS := hbudget _ (hVSmin j) z
  have hAbs : Eabs ≤ L^(2*Ca) :=
    giantSignedSourceAbsoluteEnergyConstant_le (Fintype.card S) (Fintype.card B) (ell+m)
      hL0 (mul_nonneg (Nat.cast_nonneg _) hW) hcost hBS hShi hBhi
  have hcE := hcleanBlock S PS hVS hPS (fun j i => (hsep i j).symm) n hn qStage hqStage0 hqStage1
    θ ζ ρ hζ hρ hρ1.le κ q (L^Cs) (Real.rpow_nonneg hL0.le _)
    (hsmall S PS hPS hdisS hVSmin J L hL0 hShi) reverse R V f
  have hdE := giantSignedProjectedRawDirtyFamily_rare_energy (PS:=PS) (PB:=P) (k:=J) (ell:=ell) hPS hP hdisS hsep hVS hVB ν hν V
    hvmin hVmin hVmax hmass hq hq1.le hBS hSmallBudget hρ hρ1 (v:=1) le_rfl m patterns
    idealResidualCopied hcap R kStep hk sign hsign hstepB (L^b) (L^c) hlabels
    (hgap (Fintype.card S) hShi) (fun j p hp => (hband j p hp).1) θ ζ' W hW K hK
    (fun _ _ _ => 1) (fun _ _ _ _ => by simp) f hsym
  let A := L^(-Eid) * L^Cs
  let D := 2 * Real.sqrt Eabs * Real.sqrt ε
  have hA : 0 ≤ A := mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hAhalf : A ≤ (1/2 : ℝ) * L^(-E) :=
    giantSignedSourceClean_half (Eid:=Eid) (Cs:=Cs) (smallBound:=L^Cs) hL2 le_rfl le_rfl
  have hSqrtAbs : Real.sqrt Eabs ≤ L^Ca := by
    refine (Real.sqrt_le_sqrt hAbs).trans_eq ?_
    rw [show 2 * Ca = Ca * ((2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_mul_natCast hL0.le, Real.sqrt_sq (Real.rpow_nonneg hL0.le _)]
  have hDhalf : D ≤ (1/2 : ℝ) * L^(-E) := by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSqrtAbs (by norm_num))
      (Real.sqrt_nonneg ε)).trans
    exact hgain J hJ₁ S L hL hSlo
  have hAD : A + D ≤ L^(-E) := (add_le_add hAhalf hDhalf).trans_eq (by ring)
  have he := giantSignedProjectedRawEdgeFamilyApply_split_energy (PS:=PS) (PB:=P) (k:=J) (ell:=ell) hVS ν hν V R patterns
    idealResidualCopied κ q ρ θ ζ' K (fun _ _ _ => 1) f hA hD
    (by simpa only [one_mul] using hcE) hdE
  constructor
  · exact he.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (add_nonneg hA hD) hAD 2)) le_rfl)
  · intro η hη
    have he' := giantSignedProjectedRawEdgeFamilyApply_energy (PS:=PS) (PB:=P) (k:=J) (ell:=ell) R hPS hP hdisS hVS hVB ν hν V
      hvmin hVmin hVmax hmass hq hq1.le hBS hSmallBudget hρ hρ1 (v:=1) le_rfl hW
      m patterns idealResidualCopied hcap κ θ ζ' K hK η hη f hsym
    exact he'.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hAbs) le_rfl)

end
end ArtinMatthews
