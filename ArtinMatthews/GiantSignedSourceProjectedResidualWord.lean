module

public import ArtinMatthews.GiantSignedCanonicalCleanSuccessors
public import ArtinMatthews.GiantSignedDoubledChronologicalWord
public import ArtinMatthews.GiantSignedSourceOmissionGain
public import ArtinMatthews.GiantSignedTraceEdgeAbsolute
public import ArtinMatthews.GiantSignedResidualEdgeContraction
public import ArtinMatthews.GiantSignedSharedVisitWeight
public import ArtinMatthews.GiantSignedSourceBoundaryContraction
public import ArtinMatthews.GiantSignedSourceContractionBudget
public import ArtinMatthews.GiantSignedSourceDoubledTail
public import ArtinMatthews.GiantSignedSourceTiltedBoundary
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The same constructed residual family controls the original projected
signed word and the unrestricted doubled positive boundary. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

theorem giantSignedSourceProjectedResidualWord_eventually
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
                  n patterns copied κ visitQ ζ' K (fun _ _ _ _ => 1)‖ ≤ (L ^ (-E)) ^ n ∧
                ‖giantSignedDoubledChronologicalBoundaryPairing ν V q ρ θ
                  n patterns copied κ visitQ ζ' K η‖ /
                  (2 : ℝ) ^ (R - (ell+m)*Fintype.card B*n) ≤ (L ^ (-E)) ^ n ∧
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
  obtain ⟨v, BS, hv, hBS, hweights, htail⟩ :=
    giantSignedSourceDoubledTail_eventually.{u} (C₀ := C₀) (c := c) ell
      hq hq1 hρ hρ1 hqρ hvmin hvmax hc hC₀
  let Cv := giantSignedSourceVisitExponent C₀ vmax ρ v
  let G := E + Cv + 4
  have hv0 : 0 < v := zero_lt_one.trans hv
  have hCv : 0 ≤ Cv := by unfold Cv giantSignedSourceVisitExponent; positivity
  have hG : E + Cv + 3 < G := by dsimp only [G]; linarith
  have hG0 : 0 ≤ G+2 := by dsimp only [G]; linarith
  obtain ⟨Cs,Eid,hCs,hEid,m,hm,Ca,hCa,J₀,hJ₀,hlocal⟩ :=
    giantSignedProjectedResidualEdge_contraction.{u,u} c₀ C₀ vmin vmax b c d C Cstep (G+2) 2 ell
      hq hq1 hρ.le hρ1 hc₀ hC₀ hvmin hc hbc hd hC hG0 hell
  have hEid0 : 0 ≤ Eid+1 := by linarith
  refine ⟨v,G,Cs,Eid,hv,hweights,hG,hCs,by linarith,m,hm,Ca,hCa,J₀,hJ₀,?_⟩
  intro J hJ
  have hM : 1 ≤ J+ell := hell.trans (Nat.le_add_left _ _)
  let C₁ := idealSourceCostExponent (Eid+1) C₀ vmin d C m
  have hC₁ : 0 ≤ C₁ :=
    (idealSourceParameters_nonnegative (v₀ := vmin) hEid0 hC₀ hd hC m).2.2.2.2
  filter_upwards [
    Real.tendsto_log_atTop.eventually (hlocal J hJ), htail J m hM C₁ E hC₁ hE,
    giantSignedSourceTiltedBoundary_budget_eventually q c C₀ J ell hM hq.le hq1.le hc hC₀,
    giantSignedSourceMomentLength_tendsto.eventually (eventually_ge_atTop (max 1 Cv)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (5 : ℝ))] with x hxlocal hxtail hxtilt hnlo hx
  dsimp only
  intro B _ _ PB _ hPB hdisB hVmin hVmax hinterval hband hBlo hBhi
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  have hL5 : 5 ≤ L := hx
  have hL2 : 2 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hn : 1 ≤ n := by exact_mod_cast (le_max_left (1 : ℝ) Cv).trans hnlo
  have hnCv : Cv ≤ (n : ℝ) := (le_max_right _ _).trans hnlo
  have hlen : ((n+1 : ℕ) : ℝ) ≤ L ^ (2 : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hL1 (show (13/25 : ℝ) ≤ 1 by norm_num)
    rw [Real.rpow_one] at hpow
    have hlen := giantTwoSidedSourceMomentLength_le (x := x) hL1
    change (n : ℝ) ≤ 4 * L ^ (13/25 : ℝ) at hlen
    rw [Nat.cast_add, Nat.cast_one, Real.rpow_two]
    nlinarith [mul_le_mul_of_nonneg_right hL5 hL0.le]
  obtain ⟨B₁,B₂,hmJ,hdis,hunion,hcap,hcost,hblock⟩ :=
    hxlocal B PB hPB hdisB hVmin hVmax hinterval hband hBlo hBhi
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
  have hp (g : B) (p : PB g) : Real.exp (L ^ c) ≤ (p.val : ℝ) :=
    (hband g p.val p.property).1
  have hq0i (i : Fin (n+1)) : 0 ≤ visitQ i :=
    (giantSignedSourceVisitQ_bounds hq.le hq1.le n i).1
  have hqi (i : Fin (n+1)) : visitQ i ≤ 1 := by
    have hsqrt : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq.le, Real.sqrt_nonneg q]
    exact (giantSignedSourceVisitQ_bounds hq.le hq1.le n i).2.trans hsqrt
  obtain ⟨hν,hMass,hboundary⟩ := hxtilt S B PS PB hPS hdisS hVS hVB hp hBhi
  have hlocal' (i : Fin n) (f : GiantSignedState PS PB (J+ell) → ℂ)
      (hf : ∀ s a, GiantSignedMemorySymmetric (fun mem => f (s,a,mem))) :=
    hblock S PS hPS hdisS hsep hVsmall hsmall hSlo hShi (n+1) hlen visitQ hq0i hqi
      kStep hk hkpow θ (ζ i) (hζ i) (reverse i) (sign i) (hsign i) f hf
  have hEdge (i : Fin n) (f : GiantSignedState PS PB (J+ell) → ℂ)
      (hf : ∀ s a, GiantSignedMemorySymmetric (fun mem => f (s,a,mem))) :
      giantSignedStateEnergy PS ν
        (giantSignedProjectedRawEdgeFamilyApply R ν V family idealResidualCopied
          (κ i) q ρ θ (ζ' i) (K i) (fun _ _ _ => 1) f) ≤
        ENNReal.ofReal ((L^(-G))^2) * giantSignedStateEnergy PS ν f := by
    have hb : L ^ (-(G+2)) ≤ L ^ (-G) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    exact (hlocal' i f hf).1.trans (mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (Real.rpow_nonneg hL0.le _) hb 2)) _)
  refine ⟨?_, ?_, fun i f hf => ⟨hEdge i f hf, (hlocal' i f hf).2⟩⟩
  · apply giantSignedSourceProjectedBoundaryPairing_norm_of_local PS ν hν hVS q ρ θ L Cv G E
      hL2 (by linarith [hCv]) n hn hnCv patterns copied κ ζ' K hboundary
    · intro i f hf
      exact giantSignedProjectedVisit_energy_of_source_weights PS R ν hν hMass V hvmax
        (fun g => (hVB g).le) hVmax hVS hρ hv0 (hq0i i) (hqi i) hL0 hBhi
        (hweights n i 0 le_rfl hvmax).1.le
        (fun g => (hweights n i (V g) (hVB g).le (hVmax g)).2.le) f hf
    · exact hEdge
  · have hW : 0 ≤ W := by dsimp only [W]; positivity
    have hξ : 0 < ξ := Real.rpow_pos_of_pos hL0 _
    have hK (i : Fin n) (p : IdealResidualPattern B J) (_ : p ∈ patterns i)
        (a b : MarkedPhysicalMarking PB (J+ell))
        (aux : GiantTwoSidedPatternAuxiliary PB (copied i p)) : ‖K i p a b aux‖ ≤ W :=
      giantSignedOrientedCoefficient_norm (reverse i) (idealResidualCoefficient PB Q h ξ p)
        (idealResidualCoefficient_norm PB Q h hξ p) a b aux
    exact hxtail S B (IdealResidualPattern B J) PS PB hPS hPB hdisS hVsmall hVmin hVmax
      hp hShi hBhi W hW patterns copied (fun _ => hcap) (fun _ => hcost) κ θ ζ' K hK

end
end ArtinMatthews
