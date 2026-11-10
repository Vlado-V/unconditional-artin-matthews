module

public import ArtinMatthews.GiantSignedConditionedPairing
public import ArtinMatthews.GiantSignedAmbientClean
public import ArtinMatthews.GiantSignedConditioningEnergy
public import ArtinMatthews.GiantSignedConditionedClean
public import ArtinMatthews.GiantSignedConditioningBound
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

/-! The actual all-memory conditioned clean form is absolutely summable
and has the source small-conditioning loss exactly once in norm. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (g : B) (p : PB g), NeZero p.val]

theorem giantSignedConditionedClean_pairing_bound {I : Type*} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (ζ ρ U q L : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hL : 0 ≤ L)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (Θ : MarkedPhysicalMarking PS k → ℝ) (shift : MarkedPhysicalMarking PS k → ℤ)
    (hIdeal : ∀ θ (h : MarkedPhysicalMarking PB (k+ell) → ℂ), IdealSymmetric h →
      (∑ a, giantSignedActiveMass ν a *
        ‖idealOperatorWithLaws freshLaw auxLaw patterns C θ ζ K h a‖ ^ 2) ≤
          U ^ 2 * ∑ a, giantSignedActiveMass ν a * ‖h a‖ ^ 2)
    (hSmall : ∀ f : GiantTwoSidedResidueState PS (k+ell) → ℂ,
      (∑ d : MarkedPhysicalMarking PS k,
        giantSmallResidueEnergy (giantSmallConditioningMap PS k ell q d f)) ≤
          L * giantSmallStateEnergy f)
    (w₁ w₂ : GiantSignedState PS PB (k+ell) → ℂ)
    (hw₁ : giantSignedStateEnergy PS ν w₁ ≠ ∞)
    (hw₂ : giantSignedStateEnergy PS ν w₂ ≠ ∞)
    (hsym : ∀ s m, IdealSymmetric (fun a => w₂ (s, a, m))) :
    let F := fun d => giantSignedSmallConditioning PS q d w₁
    let G := fun d => giantSignedAmbientCleanApply PS freshLaw auxLaw patterns C
      (Θ d) ζ ρ K (shift d) (giantSignedSmallConditioning PS q d w₂)
    Summable (fun i : GiantSignedConditionedIndex PS (PB := PB) k ell =>
      (giantSignedConditionedWeight PS ν i : ℂ) *
        star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i) ∧
    ENNReal.ofReal (‖giantSignedConditionedPairing PS ν F G‖ ^ 2) ≤
      ENNReal.ofReal (U ^ 2 * L ^ 2) *
        giantSignedStateEnergy PS ν w₁ * giantSignedStateEnergy PS ν w₂ := by
  let F := fun d => giantSignedSmallConditioning PS q d w₁
  let G := fun d => giantSignedAmbientCleanApply PS freshLaw auxLaw patterns C
    (Θ d) ζ ρ K (shift d) (giantSignedSmallConditioning PS q d w₂)
  have hF : giantSignedConditionedEnergy PS ν F ≤
      ENNReal.ofReal L * giantSignedStateEnergy PS ν w₁ := by
    rw [giantSignedConditionedEnergy_eq]
    exact giantSignedSmallConditioning_energy_of_bound PS hV ν hν q L hL hSmall w₁
  have hG : giantSignedConditionedEnergy PS ν G ≤
      ENNReal.ofReal (U ^ 2 * L) * giantSignedStateEnergy PS ν w₂ := by
    rw [giantSignedConditionedEnergy_eq]
    exact giantSignedConditionedClean_energy PS hV ν hν freshLaw auxLaw patterns C
      ζ ρ U q L hρ hρ1 hL K Θ shift hIdeal hSmall w₂ hsym
  have hFfin : giantSignedConditionedEnergy PS ν F ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw₁) hF
  have hGfin : giantSignedConditionedEnergy PS ν G ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw₂) hG
  constructor
  · exact giantSignedConditionedPairing_summable PS ν hν F G hFfin hGfin
  · calc
      _ ≤ giantSignedConditionedEnergy PS ν F * giantSignedConditionedEnergy PS ν G :=
        giantSignedConditionedPairing_energy PS ν hν F G hFfin hGfin
      _ ≤ (ENNReal.ofReal L * giantSignedStateEnergy PS ν w₁) *
          (ENNReal.ofReal (U ^ 2 * L) * giantSignedStateEnergy PS ν w₂) :=
        mul_le_mul' hF hG
      _ = (ENNReal.ofReal L * ENNReal.ofReal (U ^ 2 * L)) *
          giantSignedStateEnergy PS ν w₁ * giantSignedStateEnergy PS ν w₂ := by ac_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_mul hL, show L * (U ^ 2 * L) = U ^ 2 * L ^ 2 by ring]

end
end ArtinMatthews
