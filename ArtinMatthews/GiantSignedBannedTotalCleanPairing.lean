module

public import ArtinMatthews.GiantSignedAuxiliaryBan
public import ArtinMatthews.GiantSignedConditionedPairing
public import ArtinMatthews.GiantSignedConditioningEnergy
public import ArtinMatthews.GiantSignedTiltedLaw
public import ArtinMatthews.GiantSignedTotalStepClean
public import ArtinMatthews.GiantSignedBannedBandBound
public import ArtinMatthews.GiantSignedTiltBandBounds
public import ArtinMatthews.GiantSignedTotalCleanPairing
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

/-! The original harmonic contraction controls the literal total-product
clean form, including its prefix-dependent phase and signed integer step. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (g : B) (p : PB g), NeZero p.val]

theorem giantSignedBannedTotalClean_pairing_bound {I : Type*} {k ell n : ℕ}
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hP : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PB i) (PB j)))
    (v Pmin : ℝ) (hv : 0 < v) (hPmin : 0 < Pmin)
    (hVB : ∀ j, v ≤ bandReciprocalMass (PB j)) (hp : ∀ j (p : PB j), Pmin ≤ p.val)
    (qStage : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ qStage i) (hq1 : ∀ i, qStage i ≤ 1)
    (hsmall : (n : ℝ) / Pmin < 1)
    (patterns : Finset I) (C : I → B → Finset (Fin k)) (ζ ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (cost : I → ℝ) (hcost : ∀ i ∈ patterns, 0 ≤ cost i)
    (hK : ∀ i ∈ patterns, ∀ a b aux, ‖K i a b aux‖ ≤ cost i)
    (freshCount comparisonCount : ℕ)
    (hFreshCount : ∀ i ∈ patterns, (∑ j, ((C i j).card + ell)) ≤ freshCount)
    (hComparisonCount : ∀ i ∈ patterns, (∑ j, (C i j).card) * (2 * (k+ell)) ≤ comparisonCount)
    (hDensitySmall : (freshCount : ℝ) * ((n : ℝ) / Pmin) ≤ 1 / 2)
    (U : ℝ) (hU : 0 ≤ U)
    (hOriginal : ∀ θ (f : MarkedPhysicalMarking PB (k+ell) → ℂ), IdealSymmetric f →
      idealLabelEnergy PB (k+ell) (idealOperator patterns C θ ζ K f) ≤
        U ^ 2 * idealLabelEnergy PB (k+ell) f)
    (qSmall L : ℝ) (hL : 0 ≤ L)
    (hSmall : ∀ f : GiantTwoSidedResidueState PS (k+ell) → ℂ,
      (∑ d : MarkedPhysicalMarking PS k,
        giantSmallResidueEnergy (giantSmallConditioningMap PS k ell qSmall d f)) ≤
          L * giantSmallStateEnergy f)
    (θ : MarkedPhysicalMarking PS k → ℝ)
    (dNat : MarkedPhysicalMarking PS k → ℕ) (hd : ∀ d, 0 < dNat d)
    (κ : MarkedPhysicalMarking PS k → ℤ)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ)
    (hw₁ : giantSignedStateEnergy PS (fun j => giantSignedTiltedPrimeLaw (PB j) qStage) w₁ ≠ ∞)
    (hw₂ : giantSignedStateEnergy PS (fun j => giantSignedTiltedPrimeLaw (PB j) qStage) w₂ ≠ ∞)
    (hsym : ∀ s m, IdealSymmetric (fun a => w₂ (s, a, m))) :
    let ν := fun j => giantSignedTiltedPrimeLaw (PB j) qStage
    let F := fun d => giantSignedSmallConditioning PS qSmall d w₁
    let G := fun d => giantSignedTotalStepCleanApply PS ν (fun j => markedHarmonicAtom (PB j))
      patterns C (θ d) ζ ρ
      (fun i a b aux => if GiantSignedAuxiliaryBan (C i) a b aux then K i a b aux else 0)
      (dNat d) (κ d) (giantSignedSmallConditioning PS qSmall d w₂)
    let error := (∑ i ∈ patterns, cost i) * ((comparisonCount : ℝ) / (v * Pmin)) +
      (2 * (freshCount : ℝ) * ((n : ℝ) / Pmin)) * ∑ i ∈ patterns, cost i
    Summable (fun i : GiantSignedConditionedIndex PS (PB := PB) k ell =>
      (giantSignedConditionedWeight PS ν i : ℂ) *
        star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i) ∧
    ENNReal.ofReal (‖giantSignedConditionedPairing PS ν F G‖ ^ 2) ≤
      ENNReal.ofReal (((1 - (n : ℝ) / Pmin)⁻¹) ^ (Fintype.card B * (k+ell)) *
        (U + error) ^ 2 * L ^ 2) *
        giantSignedStateEnergy PS ν w₁ * giantSignedStateEnergy PS ν w₂ := by
  let ν := fun j => giantSignedTiltedPrimeLaw (PB j) qStage
  let error := (∑ i ∈ patterns, cost i) * ((comparisonCount : ℝ) / (v * Pmin)) +
    (2 * (freshCount : ℝ) * ((n : ℝ) / Pmin)) * ∑ i ∈ patterns, cost i
  let A := ((1 - (n : ℝ) / Pmin)⁻¹) ^ (Fintype.card B * (k+ell))
  let U' := Real.sqrt A * (U + error)
  let K' : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell :=
    fun i a b aux => if GiantSignedAuxiliaryBan (C i) a b aux then K i a b aux else 0
  have hA : 0 ≤ A := pow_nonneg (inv_nonneg.mpr (sub_pos.mpr hsmall).le) _
  have hsq : U' ^ 2 = A * (U + error) ^ 2 := by
    dsimp only [U']
    rw [mul_pow, Real.sq_sqrt hA]
  have hν (j : B) (p : PB j) : 0 ≤ ν j p := by
    dsimp only [ν]
    rw [giantSignedTiltedPrimeLaw_eq]
    exact mul_nonneg (markedHarmonicAtom_nonneg (PB j) (hv.trans_le (hVB j)))
      (zero_le_one.trans (giantSignedPrimeDensity_band_bounds qStage hq0 hq1
        Pmin hPmin (hp j p) hsmall).1)
  have hBetween : ∀ θ (f : MarkedPhysicalMarking PB (k+ell) → ℂ), IdealSymmetric f →
      (∑ a, giantSignedActiveMass ν a *
        ‖idealOperatorWithLaws ν (fun j => markedHarmonicAtom (PB j)) patterns C θ ζ K' f a‖ ^ 2) ≤
          U' ^ 2 * ∑ a, giantSignedActiveMass ν a * ‖f a‖ ^ 2 := by
    intro θ f hf
    rw [hsq]
    have h := giantSignedBannedIdeal_band_energy hP hdis v Pmin hv hPmin hVB hp
      qStage hq0 hq1 hsmall patterns C θ ζ K cost hcost hK freshCount comparisonCount
      hFreshCount hComparisonCount hDensitySmall U hU (hOriginal θ) f hf
    simpa only [ν, K', A, error, add_assoc] using h
  have h := giantSignedTotalClean_pairing_bound PS hVS ν hν ν
    (fun j => markedHarmonicAtom (PB j)) patterns C ζ ρ U' qSmall L hρ hρ1 hL
    K' θ dNat hd κ hBetween hSmall w₁ w₂ hw₁ hw₂ hsym
  simpa only [ν, K', hsq, A, error] using h

end
end ArtinMatthews
