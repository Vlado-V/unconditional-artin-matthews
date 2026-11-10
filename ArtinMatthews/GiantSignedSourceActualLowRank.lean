module

public import ArtinMatthews.GiantSignedActualFrameBoundary
public import ArtinMatthews.GiantSignedBirthMixedBoundary
public import ArtinMatthews.GiantSignedSourceOmissionGain
public import ArtinMatthews.GiantSignedSourceRankCutoff
public import ArtinMatthews.GiantSignedTiltedLaw
public import ArtinMatthews.GiantSignedSourceAbsoluteCost
public import ArtinMatthews.GiantSignedSourceFrameIntegralLowRank
public import ArtinMatthews.GiantSignedSourceTiltedBoundary
public import ArtinMatthews.GiantSignedTraceActual
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

/-! Sum the original capped equality events over the actual source low
ranks. All phase bounds and the tilted source measure are derived. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
universe u

local instance actualLowRankPermutationFintype {B : Type*} [Fintype B] {M n H : ℕ} :
    Fintype (Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) :=
  @Equiv.instFintype (GiantSignedUniformBirthAddress B M n H)
    (GiantSignedUniformBirthAddress B M n H) inferInstance inferInstance inferInstance inferInstance

theorem giantSignedSourceCappedBirth_low_rank_sum_eventually
    {q ρ C₀ vmin vmax v G Ca E c scale : ℝ} (k ell budget : ℕ)
    (hM : 1 ≤ k+ell) (hq : 0 < q) (hq1 : q < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hC₀ : 0 ≤ C₀) (hvmin : 0 < vmin) (hvmax : 0 ≤ vmax) (hv : 0 < v)
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
        (∀ j p, p ∈ PS j → p.Prime) → (∀ j p, p ∈ PB j → p.Prime) →
        Pairwise (fun i j => Disjoint (PS i) (PS j)) →
        (∀ j, vmin ≤ bandReciprocalMass (PS j)) →
        (∀ g, vmin ≤ bandReciprocalMass (PB g)) →
        (∀ g, bandReciprocalMass (PB g) ≤ vmax) →
        (∀ g (p : PB g), Real.exp ((Real.log x)^c) ≤ (p.val : ℝ)) →
        (Fintype.card B : ℝ) ≤ C₀ * Real.log (Real.log x) →
      let L := Real.log x
      let n := giantTwoSidedSourceMomentLength x
      let H := giantSignedSourceMemoryLimit L
      let visitQ := giantSignedSourceVisitQ q n
      let ν := fun g => giantSignedTiltedPrimeLaw (PB g) visitQ
      let V := fun g => bandReciprocalMass (PB g)
      ∀ (W : ℝ), 0 ≤ W → ∀ (θ : ℝ)
        (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k)),
        (∀ i p, p ∈ patterns i → ∀ g, (C i p g).card ≤ budget) →
      ∀ (κ : Fin n → ℤ) (ζ : Fin n → ℝ)
        (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell),
        (∀ i p, p ∈ patterns i → ∀ a b aux, ‖K i p a b aux‖ ≤ W) →
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
      (∑ σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H),
        if giantSignedUniformBirthRank σ < giantSignedSourceRankCutoff c scale x then
          ‖giantSignedCappedBirthEventBoundary (PS := PS) H ν V q ρ θ
            n patterns C κ visitQ ζ K (fun _ _ _ _ => 1) σ‖ else 0) ≤ (L^(-E))^n := by
  obtain ⟨BS,hBS,hsmall⟩ := giantSignedSmallRowBudget_exists hq hq1 hvmin ell
  filter_upwards [
    giantSignedSourceFrameIntegral_low_rank_sum_eventually k ell hM hq.le hq1.le hρ
      hC₀ hvmax hv hCa hE hc hscale hG hweights,
    giantSignedSourceTiltedBoundary_budget_eventually q c C₀ k ell hM hq.le hq1.le hc hC₀]
    with x hlow htilt
  intro S B I _ _ _ _ PS PB _ _ hPS hPB hdis hVsmall hVmin hVmax hp hgroups
  dsimp only
  intro W hW θ patterns C hCap κ ζ K hK hsigned habs
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  let H := giantSignedSourceMemoryLimit L
  let visitQ := giantSignedSourceVisitQ q n
  let ν := fun g => giantSignedTiltedPrimeLaw (PB g) visitQ
  let V := fun g => bandReciprocalMass (PB g)
  have hVS (j : S) : 0 < bandReciprocalMass (PS j) := hvmin.trans_le (hVsmall j)
  have hVB (g : B) : 0 < V g := hvmin.trans_le (hVmin g)
  obtain ⟨hν,hMass,_⟩ := htilt S B PS PB hPS hdis hVS hVB hp hgroups
  have hTrace := giantSignedChronologicalTraceRows_absolute hPS hPB hdis hVS hVB ν hν V
    hvmin hVmin hMass hq hq1.le hBS (fun j z => hsmall _ (hVsmall j) z)
    hρ.le hρ1 hW budget θ n patterns C hCap κ visitQ ζ K hK
    (fun _ _ _ _ => 1) (fun _ _ _ _ _ => by simp)
  have hb := hlow S B I PS PB hPS hdis hVS hVB hVmax hp hgroups θ patterns C κ ζ K hsigned habs
  refine le_trans (le_of_eq ?_) hb
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : giantSignedUniformBirthRank σ < giantSignedSourceRankCutoff c scale x
  · rw [ite_eq_left hσ, ite_eq_left hσ, giantSignedCappedBirthEventBoundary_eq_integral
      H ν V q ρ θ n patterns C κ visitQ ζ K (fun _ _ _ _ => 1) hTrace σ]
    simp only [giantSignedProjectedFrameBoundary, one_mul, ν, V, n, H, L, visitQ]
  · rw [ite_eq_right hσ, ite_eq_right hσ]

end
end ArtinMatthews
