module

public import ArtinMatthews.GiantSignedCleanDisintegration
public import ArtinMatthews.GiantSmallConditioningData
public import ArtinMatthews.GiantSmallConditioningActual
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

/-! The small conditioning map acts pointwise on all big labels and every
finite pending memory. The energies retain the original state masses. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

def giantSignedStateEnergy {M : ℕ} (ν : ∀ g, PB g → ℝ)
    (w : GiantSignedState PS PB M → ℂ) : ℝ≥0∞ :=
  ∑' m : GiantSignedMemory PB, ∑ s : GiantTwoSidedResidueState PS M,
    ∑ a : MarkedPhysicalMarking PB M,
      ENNReal.ofReal (giantSignedStateMass PS ν (s, a, m) * ‖w (s, a, m)‖ ^ 2)

def giantSignedSmallConditioning {k ell : ℕ} (q : ℝ)
    (d : MarkedPhysicalMarking PS k) (w : GiantSignedState PS PB (k+ell) → ℂ)
    (y : GiantTwoSidedFullResidue PS) (a : MarkedPhysicalMarking PB (k+ell))
    (m : GiantSignedMemory PB) : ℂ :=
  giantSmallConditioningMap PS k ell q d (fun s => w (s, a, m)) y

private theorem finiteEnergy_factor {X : Type*} [Fintype X]
    (c w : ℝ) (hc : 0 ≤ c) (hw : 0 ≤ w) (f : X → ℂ) :
    (∑ x, ENNReal.ofReal (c * w * ‖f x‖ ^ 2)) =
      ENNReal.ofReal w * ENNReal.ofReal (c * ∑ x, ‖f x‖ ^ 2) := by
  calc
    _ = ENNReal.ofReal (∑ x, c * w * ‖f x‖ ^ 2) :=
      (ENNReal.ofReal_sum_of_nonneg (fun x _ =>
        mul_nonneg (mul_nonneg hc hw) (sq_nonneg _))).symm
    _ = ENNReal.ofReal (w * (c * ∑ x, ‖f x‖ ^ 2)) := by
      congr 1
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := ENNReal.ofReal_mul hw

omit [DecidableEq S] in
theorem giantSignedAmbientEnergy_smallFibers {k ell : ℕ}
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB (k+ell) →
      GiantSignedMemory PB → ℂ) :
    giantSignedAmbientEnergy PS ν f =
      ∑' m : GiantSignedMemory PB, ∑ a : MarkedPhysicalMarking PB (k+ell),
        ENNReal.ofReal (giantSignedMemoryMass ν m * giantSignedActiveMass ν a) *
          ENNReal.ofReal (giantSmallResidueEnergy (fun y => f y a m)) := by
  classical
  unfold giantSignedAmbientEnergy
  apply tsum_congr
  intro m
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have hW : 0 ≤ giantSignedMemoryMass ν m * giantSignedActiveMass ν a :=
    mul_nonneg (giantSignedMemoryMass_nonneg ν hν m)
      (Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ => hν g (a g i))
  rw [giantSmallResidueEnergy_primeProduct]
  simpa only [giantSignedSmallHaar, mul_assoc] using
    finiteEnergy_factor (giantSignedSmallHaar PS)
      (giantSignedMemoryMass ν m * giantSignedActiveMass ν a)
      (giantSignedSmallHaar_nonneg PS) hW (fun y => f y a m)

theorem giantSignedStateEnergy_smallFibers {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (w : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedStateEnergy PS ν w =
      ∑' m : GiantSignedMemory PB, ∑ a : MarkedPhysicalMarking PB (k+ell),
        ENNReal.ofReal (giantSignedMemoryMass ν m * giantSignedActiveMass ν a) *
          ENNReal.ofReal (giantSmallStateEnergy (fun s => w (s, a, m))) := by
  classical
  unfold giantSignedStateEnergy
  apply tsum_congr
  intro m
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have hW : 0 ≤ giantSignedMemoryMass ν m * giantSignedActiveMass ν a :=
    mul_nonneg (giantSignedMemoryMass_nonneg ν hν m)
      (Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ => hν g (a g i))
  have hH : 0 ≤ giantTwoSidedResidueHaarStateMass PS (k+ell) := by
    unfold giantTwoSidedResidueHaarStateMass markedPhysicalMass
    exact div_nonneg
      (Finset.prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _)
      (Nat.cast_nonneg _)
  simpa only [giantSignedStateMass, giantSmallStateEnergy, mul_assoc, mul_left_comm, mul_comm] using
    finiteEnergy_factor (giantTwoSidedResidueHaarStateMass PS (k+ell))
      (giantSignedMemoryMass ν m * giantSignedActiveMass ν a) hH hW
      (fun s => w (s, a, m))

end
end ArtinMatthews
