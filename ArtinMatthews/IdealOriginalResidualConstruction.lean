module

public import ArtinMatthews.IdealResidualBlockBound
public import ArtinMatthews.IdealResidualSelectedComparison
public import ArtinMatthews.IdealOperatorSymmetricReduction
public import ArtinMatthews.IdealSourceGrowingGroups
public import ArtinMatthews.IdealSourceProbeGeometry
public import ArtinMatthews.IdealSourceProbeCaps
public import ArtinMatthews.IdealSourcePatternCost


set_option backward.privateInPublic true
@[expose] public section

/-! The residual family uses the original harmonic law and fixed
kernel parameters before the copied dimension is selected. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

theorem idealOriginalResidual_construction (c₀ C₀ v₀ c d C E : ℝ) (ell : ℕ)
    (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hv₀ : 0 < v₀) (hc : 0 < c)
    (hd : 0 ≤ d) (hC : 0 ≤ C) (hE : 0 ≤ E) (hell : 1 ≤ ell) :
    ∃ m : ℕ, 1 ≤ m ∧ 0 ≤ idealSourceCostExponent E C₀ v₀ d C m ∧
      ∀ J : ℕ, idealSourceDimensionThreshold m ell ≤ J →
        ∀ᶠ L : ℝ in atTop, ∀ (G : Type u) [Fintype G] [DecidableEq G]
          (P : G → Finset ℕ),
          (∀ g p,p∈P g → p.Prime) → Pairwise (fun g j => Disjoint (P g) (P j)) →
          (∀ g,v₀ ≤ bandReciprocalMass (P g)) → (∀ g,IdealPrimeInterval (P g)) →
          (∀ g p,p∈P g → Real.exp (L^c) ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp (L^d)) →
          c₀*Real.log L ≤ (Fintype.card G:ℝ) → (Fintype.card G:ℝ) ≤ C₀*Real.log L →
          ∃ (G₁ G₂ : Finset G) (hmJ : m ≤ J),Disjoint G₁ G₂ ∧ G₁ ∪ G₂=univ ∧
            (∀ ν∈idealResidualPatterns (idealSourceProbes G₁ hmJ) (idealSourceProbes G₂ hmJ),
              ∀ g,(idealResidualCopied ν g).card ≤ m) ∧
            (((idealResidualPatterns (idealSourceProbes G₁ hmJ) (idealSourceProbes G₂ hmJ)).card:ℝ)*
              (1+(((⌊L^(idealSourceRationalExponent E C₀ v₀ d m)⌋₊:ℕ):ℝ)^2/
                L^(-idealSourceThresholdExponent E C₀ v₀ d C m))^2) ≤
              L^(idealSourceCostExponent E C₀ v₀ d C m)) ∧
            (∀ (s t : IdealResidualPattern G J → MarkedPhysicalMarking P (J+ell))
              (aux : ∀ ν,GiantTwoSidedPatternAuxiliary P (idealResidualCopied ν)),
              (∑ ν∈idealResidualPatterns (idealSourceProbes G₁ hmJ) (idealSourceProbes G₂ hmJ),
                ‖idealResidualCoefficient P ⌊L^(idealSourceRationalExponent E C₀ v₀ d m)⌋₊
                  (L^(-idealSourceWidthExponent E C₀ v₀ d C m))
                  (L^(-idealSourceThresholdExponent E C₀ v₀ d C m)) ν (s ν) (t ν) (aux ν)‖) ≤
                L^(idealSourceCostExponent E C₀ v₀ d C m)) ∧
            (∀ Θ ζ : ℝ,|ζ| ≤ L^C → ∀ f : MarkedPhysicalMarking P (J+ell) → ℂ,
              idealLabelEnergy P (J+ell)
                (idealResidualOperator P (idealSourceProbes G₁ hmJ) (idealSourceProbes G₂ hmJ)
                  ⌊L^(idealSourceRationalExponent E C₀ v₀ d m)⌋₊
                  (L^(-idealSourceWidthExponent E C₀ v₀ d C m))
                  (L^(-idealSourceThresholdExponent E C₀ v₀ d C m)) Θ ζ f) ≤
                (L^(-E))^2*idealLabelEnergy P (J+ell) f) := by
  obtain ⟨m,hm,_hθ,_hθ1,hparams,hgroups⟩ :=
    idealSource_parameters_for_groups.{u} c₀ C₀ v₀ d C E ell hc₀ hC₀ hd hC hE
  refine ⟨m,hm,hparams.2.2.2.2,?_⟩
  intro J hJ
  obtain ⟨hmJ,hlarge,hgroupL⟩ := hgroups J hJ
  filter_upwards [hgroupL,
    idealResidualSelected_comparison.{u,u} m C₀ v₀ c d C (idealSourceErrorExponent E C₀ m)
      hC₀ hv₀ hc hd hC hparams.1,
    eventually_ge_atTop (2:ℝ)] with L hg hsel hL
  intro G _ _ P hprime hdisP hVmin hinterval hband hcardLo hcardHi
  have hV : ∀ g,0 < bandReciprocalMass (P g) := fun g => hv₀.trans_le (hVmin g)
  have hP : ∀ g p,p∈P g → 0 < p := fun g p hp => (hprime g p hp).pos
  have hLpos : 0 < L := by linarith
  obtain ⟨G₁,G₂,hdis,hunion,_hlo₁,_hlo₂,hbudget,_hcost⟩ :=
    hg G univ (by simpa only [card_univ] using hcardLo) (by simpa only [card_univ] using hcardHi)
  refine ⟨G₁,G₂,hmJ,hdis,hunion,?_,?_,?_,?_⟩
  · intro ν hν g
    exact idealSourceResidualCopied_card_le G₁ G₂ hmJ ν hν g
  · exact idealSource_pattern_constant_cost G₁ G₂ univ hmJ hdis hunion hE hC₀ hd hC hL
      (by simpa only [card_univ] using hcardHi)
  · intro s t aux
    exact idealSource_coefficient_cost P G₁ G₂ univ hmJ hdis hunion hE hC₀ hd hC hL
      (by simpa only [card_univ] using hcardHi) s t aux
  · intro Θ ζ hζ f
    let S := idealSourceProbes G₁ hmJ
    let T := idealSourceProbes G₂ hmJ
    let Q := ⌊L^(idealSourceRationalExponent E C₀ v₀ d m)⌋₊
    let w := L^(-idealSourceWidthExponent E C₀ v₀ d C m)
    let ξ := L^(-idealSourceThresholdExponent E C₀ v₀ d C m)
    let ε := L^(-idealSourceErrorExponent E C₀ m)
    let Op : (MarkedPhysicalMarking P (J+ell) → ℂ) → MarkedPhysicalMarking P (J+ell) → ℂ :=
      idealResidualOperator (ell:=ell) P S T Q w ξ Θ ζ
    have hST : Disjoint S T := idealSourceProbes_disjoint G₁ G₂ hmJ hdis
    have hcmp (A : Finset (G × Fin J)) (hA : A∈S.powerset.erase ∅)
        (B : Finset (G × Fin J)) (hB : B∈T.powerset.erase ∅) :
        ∀ α u v,‖idealSelectedComparisonForm (idealResidualBands P A) (idealResidualBands P B) Q w ξ ζ α u v‖ ≤
          ε*Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P A)) u)*
            Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P B)) v) := by
      have ha := mem_powerset.mp (mem_of_mem_erase hA)
      have hb := mem_powerset.mp (mem_of_mem_erase hB)
      obtain ⟨a,ha'⟩ := nonempty_iff_ne_empty.mpr (mem_erase.mp hA).1
      obtain ⟨b,hb'⟩ := nonempty_iff_ne_empty.mpr (mem_erase.mp hB).1
      intro α u v
      have hs := hsel G G P P J J A B hprime hprime hdisP hdisP hVmin hVmin
        (idealSource_freeSlots_card_le G₁ hmJ A ha)
        (idealSource_freeSlots_card_le G₂ hmJ B hb)
        hcardHi hcardHi hband hband ⟨a,ha'⟩ ⟨b,hb'⟩ (hinterval a.1) (hinterval b.1) ζ α hζ u v
      simpa only [Q,w,ξ,ε,idealSourceRationalExponent,idealSourceWidthExponent,idealSourceThresholdExponent] using hs
    have hfactor :
        Real.sqrt (((2:ℝ)/(m+1:ℕ))^G₁.card)+Real.sqrt (((2:ℝ)/(m+1:ℕ))^G₂.card)+
          (2:ℝ)^(S.card+T.card)*ε ≤ L^(-E) := by
      dsimp only [S,T,ε]
      rw [idealSourceProbes_total_card G₁ G₂ univ hmJ hdis hunion]
      exact hbudget
    have hpairs (u v : MarkedPhysicalMarking P (J+ell) → ℂ)
        (hu : IdealSymmetric u) (hv : IdealSymmetric v) :
        ‖idealLabelPairing P u (Op v)‖ ≤ L^(-E)*idealLabelNorm P u*idealLabelNorm P v := by
      have hb := idealResidualOperator_block_pairing P hV hP S T hST
        (fun _ => idealSourceFullProbeSlots hmJ ell) (fun _ => idealSourceTailSlots J ell) G₁ G₂
        (idealSourceFullProbeSlots_included G₁ hmJ ell)
        (idealSourceFullProbeSlots_included G₂ hmJ ell)
        (idealSourceTailSlots_included J ell)
        (fun _ => idealSourceFullProbeSlots_disjoint hmJ ell) hm hell
        (fun _ => idealSourceFullProbeSlots_card hmJ ell)
        (fun _ => idealSourceTailSlots_card J ell) hlarge Q w ξ Θ ζ
        (Real.rpow_nonneg hLpos.le _) hcmp u v hu hv
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfactor (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    have hout (u : MarkedPhysicalMarking P (J+ell) → ℂ) : IdealSymmetric (Op u) := by
      dsimp only [Op,idealResidualOperator,idealOperator]
      exact idealOperatorWithLaws_symmetric (P:=P) (k:=J) (ell:=ell)
        (fun j => markedHarmonicAtom (P j)) (fun j => markedHarmonicAtom (P j))
        (idealResidualPatterns S T) idealResidualCopied Θ ζ (idealResidualCoefficient P Q w ξ) u
    have hsymmetric (u : MarkedPhysicalMarking P (J+ell) → ℂ) (hu : IdealSymmetric u) :
        idealLabelEnergy P (J+ell) (Op u) ≤ (L^(-E))^2*idealLabelEnergy P (J+ell) u :=
      idealOperator_energy_of_symmetric_pairings P (M:=J+ell) hV Op (fun u _ => hout u)
        (Real.rpow_nonneg hLpos.le _) hpairs u hu
    have hfull := idealOperatorWithLaws_energy_from_symmetric P (k:=J) (ell:=ell) hV
      (fun j => markedHarmonicAtom (P j)) (fun j => markedHarmonicAtom (P j))
      (idealResidualPatterns S T) idealResidualCopied Θ ζ (idealResidualCoefficient P Q w ξ)
      (sq_nonneg (L^(-E))) hsymmetric f
    exact hfull

end
end ArtinMatthews
