module

public import ArtinMatthews.GiantSignedBirthMixedBoundary
public import ArtinMatthews.GiantSignedLocalBirthPhase
public import ArtinMatthews.GiantSignedSourceOmissionGain
public import ArtinMatthews.GiantSignedSourceRankCutoff
public import ArtinMatthews.GiantSignedSourceVisitEnergy
public import ArtinMatthews.GiantSignedTiltedLaw
public import ArtinMatthews.GiantSignedSourceFrameIntegralNorm
public import ArtinMatthews.GiantSignedSourceLowRankBudget
public import ArtinMatthews.GiantSignedSourceTiltedBoundary
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The actual capped source phase integrals sum over low ranks with
the original signed edge savings and original Haar and tilted masses. -/
namespace ArtinMatthews
open Filter MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
universe u

local instance sourceIntegralLowRankPermutationFintype {B : Type*} [Fintype B] {M n H : ℕ} :
    Fintype (Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) :=
  @Equiv.instFintype (GiantSignedUniformBirthAddress B M n H)
    (GiantSignedUniformBirthAddress B M n H) inferInstance inferInstance inferInstance inferInstance

theorem giantSignedSourceFrameIntegral_low_rank_sum_eventually
    {q ρ C₀ vmax v G Ca E c scale : ℝ} (k ell : ℕ)
    (hM : 1 ≤ k+ell) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ)
    (hC₀ : 0 ≤ C₀) (hvmax : 0 ≤ vmax) (hv : 0 < v)
    (hCa : 0 ≤ Ca) (hE : 0 ≤ E) (hc : 0 < c) (hscale : 0 ≤ scale)
    (hG : E + giantSignedSourceVisitExponent C₀ vmax ρ v + 3 < G)
    (hweights : ∀ (n : ℕ) (i : Fin (n+1)) (Vg : ℝ), 0 ≤ Vg → Vg ≤ vmax →
      |giantSignedSourceVisitQ q n i / ρ ^ 2| +
        |-(1-giantSignedSourceVisitQ q n i) / ρ| / v < 1 ∧
      |giantSignedSourceVisitQ q n i / ρ ^ 2| +
        2 * |-(1-giantSignedSourceVisitQ q n i) * Vg / ρ| / v < 1) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (S B I : Type u) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
        (PS : S → Finset ℕ) (PB : B → Finset ℕ)
        [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
        [∀ g, ∀ p : PB g, NeZero p.val],
        (∀ j p, p ∈ PS j → p.Prime) →
        Pairwise (fun i j => Disjoint (PS i) (PS j)) →
        (∀ j, 0 < bandReciprocalMass (PS j)) →
        (∀ g, 0 < bandReciprocalMass (PB g)) →
        (∀ g, bandReciprocalMass (PB g) ≤ vmax) →
        (∀ g (p : PB g), Real.exp ((Real.log x)^c) ≤ (p.val : ℝ)) →
        (Fintype.card B : ℝ) ≤ C₀ * Real.log (Real.log x) →
      let L := Real.log x
      let n := giantTwoSidedSourceMomentLength x
      let H := giantSignedSourceMemoryLimit L
      let visitQ := giantSignedSourceVisitQ q n
      let ν := fun g => giantSignedTiltedPrimeLaw (PB g) visitQ
      let V := fun g => bandReciprocalMass (PB g)
      ∀ (θ : ℝ) (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
        (κ : Fin n → ℤ) (ζ : Fin n → ℝ)
        (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell),
        (∀ (i : Fin n) (w : GiantSignedState PS PB (k+ell) → ℂ),
          (∀ s a, GiantSignedMemorySymmetric (fun mem => w (s,a,mem))) →
          giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply H ν V
            (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (fun _ _ _ => 1) w) ≤
            ENNReal.ofReal ((L^(-G))^2) * giantSignedStateEnergy PS ν w) →
        (∀ (i : Fin n) (w : GiantSignedState PS PB (k+ell) → ℂ),
          (∀ s a, GiantSignedMemorySymmetric (fun mem => w (s,a,mem))) →
          ∀ (η : (p : I) → (s : GiantSignedState PS PB (k+ell)) →
            GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2 → ℂ),
            (∀ p ∈ patterns i, ∀ s r, ‖η p s r‖ ≤ 1) →
            giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply H ν V
              (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) η w) ≤
              ENNReal.ofReal (L^(2*Ca)) * giantSignedStateEnergy PS ν w) →
      let A := GiantSignedUniformBirthAddress B (k+ell) n H
      (∑ σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H),
        if giantSignedUniformBirthRank σ < giantSignedSourceRankCutoff c scale x then
          ‖∫ τ : A → AddCircle (1 : ℝ),
            giantSignedProjectedBirthBoundaryPairing (PS := PS) H ν V q ρ θ n patterns C κ visitQ ζ K
              (fun i _ s r => giantSignedRawEdgeFramePhase σ τ i s r)
              (giantSignedVisitFramePhase σ τ) (giantSignedInitialFramePhase σ τ)
            ∂Measure.pi (fun _ => AddCircle.haarAddCircle)‖ else 0) ≤ (L^(-E))^n := by
  let Cv := giantSignedSourceVisitExponent C₀ vmax ρ v
  have hCv : 0 ≤ Cv := by unfold Cv giantSignedSourceVisitExponent; positivity
  have hG0 : 0 ≤ G := by change E+Cv+3 < G at hG; linarith
  filter_upwards [
    giantSignedSourceBirth_low_rank_sum_eventually C₀ Cv G Ca E c scale (k+ell)
      hC₀ hCv hCa hE hG hc hscale,
    giantSignedSourceRankCutoff_le_fraction hc hscale (by norm_num : 0 < (1/2 : ℝ)),
    giantSignedSourceTiltedBoundary_budget_eventually q c C₀ k ell hM hq0 hq1 hc hC₀,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hlow hcut htilt hL
  intro S B I _ _ _ _ PS PB _ _ hPS hdis hVS hVB hVmax hp hgroups
  dsimp only
  intro θ patterns C κ ζ K hsigned habs
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  let H := giantSignedSourceMemoryLimit L
  let visitQ := giantSignedSourceVisitQ q n
  let ν := fun g => giantSignedTiltedPrimeLaw (PB g) visitQ
  let V := fun g => bandReciprocalMass (PB g)
  let A := GiantSignedUniformBirthAddress B (k+ell) n H
  obtain ⟨hν,hMass,hboundary⟩ := htilt S B PS PB hPS hdis hVS hVB hp hgroups
  let F (σ : Equiv.Perm A) :=
    ∫ τ : A → AddCircle (1 : ℝ),
      giantSignedProjectedBirthBoundaryPairing (PS := PS) H ν V q ρ θ n patterns C κ visitQ ζ K
        (fun i _ s r => giantSignedRawEdgeFramePhase σ τ i s r)
        (giantSignedVisitFramePhase σ τ) (giantSignedInitialFramePhase σ τ)
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)
  refine hlow B hgroups F ?_
  intro σ hσ
  let r := giantSignedUniformBirthRank σ
  have hr' : (r : ℝ) ≤ (giantSignedSourceRankCutoff c scale x : ℝ) :=
    by exact_mod_cast (Nat.le_of_lt hσ)
  have hr : 2*r ≤ n := by
    change (giantSignedSourceRankCutoff c scale x : ℝ) ≤ (1/2 : ℝ)*(n : ℝ) at hcut
    exact_mod_cast (show 2*(r : ℝ) ≤ (n : ℝ) by linarith)
  exact giantSignedSourceFramePhaseIntegral_norm PS ν hν hMass hVS
    hq0 hq1 hρ hv hL hG0 hCa hvmax (fun g => (hVB g).le) hVmax hgroups
    θ patterns C κ ζ K σ hr hboundary (hweights n) hsigned habs

end
end ArtinMatthews
