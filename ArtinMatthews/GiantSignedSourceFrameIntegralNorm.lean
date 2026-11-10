module

public import ArtinMatthews.GiantSignedBirthMixedBoundary
public import ArtinMatthews.GiantSignedLocalBirthPhase
public import ArtinMatthews.GiantSignedSourceOmissionGain
public import ArtinMatthews.GiantSignedSourceVisitEnergy
public import ArtinMatthews.GiantSignedSourceFramePhaseNorm
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

/-! Integrate the actual bounded phase word on its literal probability
space. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
universe u

variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {k ell n : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedSourceFramePhaseIntegral_norm
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ 2)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    {q ρ L C₀ vmax v G Ca : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hρ : 0 < ρ) (hv : 0 < v) (hL1 : 1 ≤ L)
    (hG : 0 ≤ G) (hCa : 0 ≤ Ca) (hvmax : 0 ≤ vmax)
    (hV0 : ∀ g, 0 ≤ bandReciprocalMass (PB g))
    (hVmax : ∀ g, bandReciprocalMass (PB g) ≤ vmax)
    (hgroups : (Fintype.card B : ℝ) ≤ C₀ * Real.log L)
    (θ : ℝ) (patterns : Fin n → Finset I)
    (C : Fin n → I → B → Finset (Fin k)) (κ : Fin n → ℤ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n (giantSignedSourceMemoryLimit L)))
    (hr : 2 * giantSignedUniformBirthRank σ ≤ n)
    (hboundary : giantSignedStateEnergy PS ν (giantSignedBoundary (M := k+ell)) ≤ 2) :
    let V := fun g => bandReciprocalMass (PB g)
    let H := giantSignedSourceMemoryLimit L
    let visitQ := giantSignedSourceVisitQ q n
    let Cv := giantSignedSourceVisitExponent C₀ vmax ρ v
    (∀ (i : Fin (n+1)) (Vg : ℝ), 0 ≤ Vg → Vg ≤ vmax →
      |visitQ i / ρ ^ 2| + |-(1-visitQ i) / ρ| / v < 1 ∧
      |visitQ i / ρ ^ 2| + 2 * |-(1-visitQ i) * Vg / ρ| / v < 1) →
    (∀ (i : Fin n) (w : GiantSignedState PS PB (k+ell) → ℂ),
      (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
      giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply H ν V
        (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (fun _ _ _ => 1) w) ≤
        ENNReal.ofReal ((L^(-G))^2) * giantSignedStateEnergy PS ν w) →
    (∀ (i : Fin n) (w : GiantSignedState PS PB (k+ell) → ℂ),
      (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
      ∀ (η : (p : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2 → ℂ),
        (∀ p ∈ patterns i, ∀ s r, ‖η p s r‖ ≤ 1) →
        giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply H ν V
          (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) η w) ≤
          ENNReal.ofReal (L^(2*Ca)) * giantSignedStateEnergy PS ν w) →
    let A := GiantSignedUniformBirthAddress B (k+ell) n H
    let r := giantSignedUniformBirthRank σ
    ‖∫ τ : A → AddCircle (1 : ℝ),
      giantSignedProjectedBirthBoundaryPairing (PS := PS) H ν V q ρ θ n patterns C κ visitQ ζ K
        (fun i _ s r => giantSignedRawEdgeFramePhase σ τ i s r)
        (giantSignedVisitFramePhase σ τ) (giantSignedInitialFramePhase σ τ)
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)‖ ≤
      2*(L^(Cv/2))^(n+1)*(L^(-G))^(n-2*r)*(L^Ca)^(2*r) := by
  dsimp only
  intro hweights hsigned habs
  let H := giantSignedSourceMemoryLimit L
  let V := fun g => bandReciprocalMass (PB g)
  let visitQ := giantSignedSourceVisitQ q n
  let A := GiantSignedUniformBirthAddress B (k+ell) n H
  let μ := Measure.pi (fun _ : A => @AddCircle.haarAddCircle (1 : ℝ) inferInstance)
  let F (τ : A → AddCircle (1 : ℝ)) :=
    giantSignedProjectedBirthBoundaryPairing (PS := PS) H ν V q ρ θ n patterns C κ visitQ ζ K
      (fun i _ s r => giantSignedRawEdgeFramePhase σ τ i s r)
      (giantSignedVisitFramePhase σ τ) (giantSignedInitialFramePhase σ τ)
  let Cv := giantSignedSourceVisitExponent C₀ vmax ρ v
  let r := giantSignedUniformBirthRank σ
  let T := 2*(L^(Cv/2))^(n+1)*(L^(-G))^(n-2*r)*(L^Ca)^(2*r)
  have hτ (τ : A → AddCircle (1 : ℝ)) : ‖F τ‖ ≤ T := by
    exact giantSignedSourceFramePhaseBoundary_norm PS ν hν hMass hVS hq0 hq1 hρ hv hL1
      hG hCa hvmax hV0 hVmax hgroups θ patterns C κ ζ K σ hr τ hboundary hweights hsigned habs
  change ‖∫ τ, F τ ∂μ‖ ≤ T
  simpa only [μ, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hτ)

end
end ArtinMatthews
