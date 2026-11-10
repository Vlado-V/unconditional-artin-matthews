module

public import ArtinMatthews.GiantSignedAmbientClean
public import ArtinMatthews.GiantSignedConditioningEnergy
public import ArtinMatthews.GiantSignedConditioningBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Conditioning preserves big-label symmetry and the exact clean row
acts on each conditioned function with its original residue translation. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (g : B) (p : PB g), NeZero p.val]

omit [Fintype B] [DecidableEq B]
  [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
  [∀ (g : B) (p : PB g), NeZero p.val] in
theorem giantSignedSmallConditioning_symmetric {k ell : ℕ}
    (q : ℝ) (d : MarkedPhysicalMarking PS k)
    (w : GiantSignedState PS PB (k+ell) → ℂ)
    (hw : ∀ s m, IdealSymmetric (fun a => w (s, a, m)))
    (y : GiantTwoSidedFullResidue PS) (m : GiantSignedMemory PB) :
    IdealSymmetric (fun a => giantSignedSmallConditioning PS q d w y a m) := by
  intro π a
  unfold giantSignedSmallConditioning
  dsimp only
  have h : (fun s => w (s, giantTwoSidedPermuteLabels π a, m)) =
      (fun s => w (s, a, m)) := funext fun s => hw s m π a
  rw [h]

omit [Fintype B] [DecidableEq B]
  [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
  [∀ (g : B) (p : PB g), NeZero p.val] in
theorem giantSignedSmallConditioning_memorySymmetric {k ell : ℕ}
    (q : ℝ) (d : MarkedPhysicalMarking PS k)
    (w : GiantSignedState PS PB (k+ell) → ℂ)
    (hw : ∀ s a, GiantSignedMemorySymmetric (fun m => w (s, a, m)))
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k+ell)) :
    GiantSignedMemorySymmetric (fun m => giantSignedSmallConditioning PS q d w y a m) := by
  intro m σ
  unfold giantSignedSmallConditioning
  dsimp only
  have h : (fun s => w (s, a, giantSignedMemoryPermute m σ)) =
      (fun s => w (s, a, m)) := funext fun s => hw s a m σ
  rw [h]

theorem giantSignedConditionedClean_energy {I : Type*} {k ell : ℕ}
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
    (w : GiantSignedState PS PB (k+ell) → ℂ)
    (hw : ∀ s m, IdealSymmetric (fun a => w (s, a, m))) :
    (∑ d : MarkedPhysicalMarking PS k,
      giantSignedAmbientEnergy PS ν
        (giantSignedAmbientCleanApply PS freshLaw auxLaw patterns C (Θ d) ζ ρ K (shift d)
          (giantSignedSmallConditioning PS q d w))) ≤
      ENNReal.ofReal (U ^ 2 * L) * giantSignedStateEnergy PS ν w := by
  calc
    _ ≤ ∑ d : MarkedPhysicalMarking PS k,
        ENNReal.ofReal (U ^ 2) *
          giantSignedAmbientEnergy PS ν (giantSignedSmallConditioning PS q d w) := by
      apply Finset.sum_le_sum
      intro d _
      exact giantSignedAmbientCleanApply_energy PS ν hν freshLaw auxLaw patterns C
        (Θ d) ζ ρ U hρ hρ1 K (shift d) hIdeal _
        (giantSignedSmallConditioning_symmetric PS q d w hw)
    _ = ENNReal.ofReal (U ^ 2) *
        ∑ d : MarkedPhysicalMarking PS k,
          giantSignedAmbientEnergy PS ν (giantSignedSmallConditioning PS q d w) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal (U ^ 2) *
        (ENNReal.ofReal L * giantSignedStateEnergy PS ν w) :=
      mul_le_mul_right (giantSignedSmallConditioning_energy_of_bound PS hV ν hν q L hL hSmall w) _
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg U)]

end
end ArtinMatthews
