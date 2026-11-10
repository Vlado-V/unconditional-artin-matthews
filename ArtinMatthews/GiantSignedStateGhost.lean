module

public import ArtinMatthews.GiantSignedConditioningEnergy
public import ArtinMatthews.GiantSignedGhostSimultaneous
public import ArtinMatthews.GiantSignedGhostMemoryActual
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

/-! The original simultaneous ghost acts on each actual small-state
and active-label fiber. Its energy retains the original full state mass. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

def giantSignedStateGhostApply {M : ℕ} (ν : ∀ g, PB g → ℝ) (A C D : B → ℂ)
    (w : GiantSignedState PS PB M → ℂ) (s : GiantSignedState PS PB M) : ℂ :=
  giantSignedGhostSimultaneousApply ν A C D (fun m => w (s.1, s.2.1, m)) s.2.2

theorem giantSignedStateEnergy_memoryFibers {M : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (w : GiantSignedState PS PB M → ℂ) :
    giantSignedStateEnergy PS ν w =
      ∑ s : GiantTwoSidedResidueState PS M, ∑ a : MarkedPhysicalMarking PB M,
        ENNReal.ofReal (giantTwoSidedResidueHaarStateMass PS M * giantSignedActiveMass ν a) *
          giantSignedGhostMemoryEnergy ν (fun m => w (s, a, m)) := by
  have hH : 0 ≤ giantTwoSidedResidueHaarStateMass PS M := by
    unfold giantTwoSidedResidueHaarStateMass markedPhysicalMass
    exact div_nonneg
      (Finset.prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _)
      (Nat.cast_nonneg _)
  have hA (a : MarkedPhysicalMarking PB M) : 0 ≤ giantSignedActiveMass ν a :=
    Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ => hν g (a g i)
  unfold giantSignedStateEnergy
  calc
    _ = ∑' m : GiantSignedMemory PB, ∑' s : GiantTwoSidedResidueState PS M,
        ∑' a : MarkedPhysicalMarking PB M,
          ENNReal.ofReal (giantSignedStateMass PS ν (s, a, m) * ‖w (s, a, m)‖ ^ 2) := by
      simp only [tsum_fintype]
    _ = ∑' s : GiantTwoSidedResidueState PS M, ∑' a : MarkedPhysicalMarking PB M,
        ∑' m : GiantSignedMemory PB,
          ENNReal.ofReal (giantSignedStateMass PS ν (s, a, m) * ‖w (s, a, m)‖ ^ 2) := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro s
      exact ENNReal.tsum_comm
    _ = _ := by
      simp only [tsum_fintype]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro a _
      unfold giantSignedGhostMemoryEnergy
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro m
      rw [← ENNReal.ofReal_mul (mul_nonneg hH (hA a))]
      congr 1
      unfold giantSignedStateMass
      ring

omit [DecidableEq S] [DecidableEq B]
  [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] in
theorem giantSignedStateGhostApply_activeSymmetric {M : ℕ}
    (ν : ∀ g, PB g → ℝ) (A C D : B → ℂ)
    (w : GiantSignedState PS PB M → ℂ)
    (hw : ∀ s m, IdealSymmetric (fun a => w (s, a, m)))
    (s : GiantTwoSidedResidueState PS M) (m : GiantSignedMemory PB) :
    IdealSymmetric (fun a => giantSignedStateGhostApply PS ν A C D w (s, a, m)) := by
  intro π a
  change giantSignedGhostSimultaneousApply ν A C D
      (fun m' => w (s, giantTwoSidedPermuteLabels π a, m')) m =
    giantSignedGhostSimultaneousApply ν A C D (fun m' => w (s, a, m')) m
  have he : (fun m' => w (s, giantTwoSidedPermuteLabels π a, m')) =
      (fun m' => w (s, a, m')) := funext fun m' => hw s m' π a
  rw [he]

variable [∀ (g : B) (p : PB g), NeZero p.val]

omit [DecidableEq S] [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
  [∀ (g : B) (p : PB g), NeZero p.val] in
theorem giantSignedStateGhostApply_memorySymmetric {M : ℕ}
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (w : GiantSignedState PS PB M → ℂ)
    (hws : ∀ s a, GiantSignedMemorySymmetric (fun m => w (s, a, m)))
    (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hw : ∀ s a m, ‖w (s, a, m)‖ ≤ Cf * u ^ (∑ g, m.1 g))
    (s : GiantTwoSidedResidueState PS M) (a : MarkedPhysicalMarking PB M) :
    GiantSignedMemorySymmetric (fun m => giantSignedStateGhostApply PS ν A C D w (s, a, m)) :=
  giantSignedGhostSimultaneous_symmetric ν hν A C D (fun m => w (s, a, m))
    (hws s a) Cf u hCf hu (hw s a)

theorem giantSignedStateGhostApply_energy {M : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (v : ℝ) (hv : 0 < v)
    (hrow : ∀ g, ‖A g‖ + ‖D g‖ / v ≤ 1) (hcol : ∀ g, ‖A g‖ + ‖C g‖ / v ≤ 1)
    (w : GiantSignedState PS PB M → ℂ)
    (hws : ∀ s a, GiantSignedMemorySymmetric (fun m => w (s, a, m)))
    (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hw : ∀ s a m, ‖w (s, a, m)‖ ≤ Cf * u ^ (∑ g, m.1 g)) :
    giantSignedStateEnergy PS ν (giantSignedStateGhostApply PS ν A C D w) ≤
      (∏ g, ENNReal.ofReal (Real.exp ((‖C g‖ + ‖D g‖) * (∑ p : PB g, ν g p) * v))) *
        giantSignedStateEnergy PS ν w := by
  rw [giantSignedStateEnergy_memoryFibers PS hV ν hν,
    giantSignedStateEnergy_memoryFibers PS hV ν hν]
  calc
    _ ≤ ∑ s : GiantTwoSidedResidueState PS M, ∑ a : MarkedPhysicalMarking PB M,
        ENNReal.ofReal (giantTwoSidedResidueHaarStateMass PS M * giantSignedActiveMass ν a) *
          ((∏ g, ENNReal.ofReal (Real.exp ((‖C g‖ + ‖D g‖) * (∑ p : PB g, ν g p) * v))) *
            giantSignedGhostMemoryEnergy ν (fun m => w (s, a, m))) := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_right (giantSignedGhostSimultaneous_energy ν hν A C D v hv hrow hcol
        (fun m => w (s, a, m)) (hws s a) Cf u hCf hu (hw s a)) _
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro a _
      ac_rfl

end
end ArtinMatthews
