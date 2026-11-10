module

public import ArtinMatthews.GiantSignedCleanSectorJoint
public import ArtinMatthews.GiantSignedConditionedPairing
public import ArtinMatthews.GiantSignedConditioningEnergy
public import ArtinMatthews.GiantSignedCleanSectorReindex
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

/-! The literal ordered-prefix clean tail form is summed over every
pending sector and identified with the actual total-step pairing. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (j : B) (p : PB j), NeZero p.val]

def giantSignedFullCleanForm {I : Type*} {k ell : ℕ}
    (ν freshLaw auxLaw : ∀ j, PB j → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ q : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) (κ : ℤ)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ) : ℂ :=
  ∑' s : GiantSignedMemorySectors PB,
    giantSignedSectorTailForm PS ν freshLaw auxLaw patterns C θ ζ ρ q K κ s w₁ w₂

theorem giantSignedFullCleanForm_eq_pairing {I : Type*} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν freshLaw auxLaw : ∀ j, PB j → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ q : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) (κ : ℤ)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ)
    (hs : let F := fun d => giantSignedSmallConditioning PS q d w₁
      let G := fun d => giantSignedTotalStepCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K
        (markedPhysicalMarkingProduct d) κ (giantSignedSmallConditioning PS q d w₂)
      Summable (fun i : GiantSignedConditionedIndex PS (PB := PB) k ell =>
        (giantSignedConditionedWeight PS ν i : ℂ) *
          star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i)) :
    giantSignedFullCleanForm PS ν freshLaw auxLaw patterns C θ ζ ρ q K κ w₁ w₂ =
      giantSignedConditionedPairing PS ν (fun d => giantSignedSmallConditioning PS q d w₁)
        (fun d => giantSignedTotalStepCleanApply PS freshLaw auxLaw patterns C θ ζ ρ K
          (markedPhysicalMarkingProduct d) κ (giantSignedSmallConditioning PS q d w₂)) := by
  rw [giantSignedConditionedPairing_sector PS ν _ _ hs]
  unfold giantSignedFullCleanForm
  apply tsum_congr
  intro s
  rw [giantSignedSectorTailForm_eq_conditioned PS hV]
  unfold giantSignedSectorConditionedForm
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  rw [giantSignedTotalStepCleanApply_sector PS freshLaw auxLaw patterns C θ ζ ρ K d κ]
  rfl

theorem giantSignedFullCleanForm_energy {I : Type*} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (hP : ∀ j p, p ∈ PS j → p.Prime)
    (ν : ∀ j, PB j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (freshLaw auxLaw : ∀ j, PB j → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (θ ζ ρ q U L : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hL : 0 ≤ L)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) (κ : ℤ)
    (hIdeal : ∀ Θ (h : MarkedPhysicalMarking PB (k+ell) → ℂ), IdealSymmetric h →
      (∑ a, giantSignedActiveMass ν a *
        ‖idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ K h a‖ ^ 2) ≤
          U ^ 2 * ∑ a, giantSignedActiveMass ν a * ‖h a‖ ^ 2)
    (hSmall : ∀ f : GiantTwoSidedResidueState PS (k+ell) → ℂ,
      (∑ d : MarkedPhysicalMarking PS k,
        giantSmallResidueEnergy (giantSmallConditioningMap PS k ell q d f)) ≤
          L * giantSmallStateEnergy f)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ)
    (hw₁ : giantSignedStateEnergy PS ν w₁ ≠ ∞)
    (hw₂ : giantSignedStateEnergy PS ν w₂ ≠ ∞)
    (hsym : ∀ s m, IdealSymmetric (fun a => w₂ (s, a, m))) :
    ENNReal.ofReal (‖giantSignedFullCleanForm PS ν freshLaw auxLaw patterns C θ ζ ρ q K κ w₁ w₂‖ ^ 2) ≤
      ENNReal.ofReal (U ^ 2 * L ^ 2) *
        giantSignedStateEnergy PS ν w₁ * giantSignedStateEnergy PS ν w₂ := by
  have h := giantSignedTotalClean_pairing_bound PS hV ν hν freshLaw auxLaw patterns C ζ ρ U q L
    hρ hρ1 hL K (fun _ => θ) markedPhysicalMarkingProduct
    (giantSignedSmallPrefixProduct_pos hP) (fun _ => κ) hIdeal hSmall w₁ w₂ hw₁ hw₂ hsym
  rw [giantSignedFullCleanForm_eq_pairing PS hV ν freshLaw auxLaw patterns C θ ζ ρ q K κ w₁ w₂ h.1]
  exact h.2

end
end ArtinMatthews
