module

public import ArtinMatthews.GiantSignedStateSlotPairing
public import ArtinMatthews.GiantSignedPairingEnergy
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The pairing and its norm test use the same small Haar mass, active
product law and factorial pending-memory measure as the raw edge. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

def giantSignedStatePairing (ν : ∀ g, PB g → ℝ)
    (f g : GiantSignedState PS PB M → ℂ) : ℂ :=
  ∑' m : GiantSignedMemory PB, giantSignedStateFiberPairing PS ν f g m

private theorem stateMass_nonneg
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (s : GiantSignedState PS PB M) :
    0 ≤ giantSignedStateMass PS ν s := by
  apply mul_nonneg
  · apply mul_nonneg
    · unfold giantTwoSidedResidueHaarStateMass markedPhysicalMass
      exact div_nonneg
        (Finset.prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hVS j).le) _)
        (Nat.cast_nonneg _)
    · exact Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ => hν g (s.2.1 g i)
  · exact giantSignedMemoryMass_nonneg ν hν s.2.2

theorem giantSignedStatePairing_summable
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (f g : GiantSignedState PS PB M → ℂ)
    (hf : giantSignedStateEnergy PS ν f ≠ ∞) (hg : giantSignedStateEnergy PS ν g ≠ ∞) :
    Summable (fun s => (giantSignedStateMass PS ν s : ℂ) * star (f s) * g s) := by
  rw [giantSignedStateEnergy_eq_tsum] at hf hg
  exact giantSignedWeightedPairing_summable_of_energy (giantSignedStateMass PS ν)
    (stateMass_nonneg PS hVS ν hν) f g hf hg

theorem giantSignedStatePairing_eq_tsum (ν : ∀ g, PB g → ℝ)
    (f g : GiantSignedState PS PB M → ℂ)
    (hs : Summable (fun s => (giantSignedStateMass PS ν s : ℂ) * star (f s) * g s)) :
    giantSignedStatePairing PS ν f g =
      ∑' s, (giantSignedStateMass PS ν s : ℂ) * star (f s) * g s := by
  let X := GiantSignedMemory PB × (GiantTwoSidedResidueState PS M × MarkedPhysicalMarking PB M)
  let e : X ≃ GiantSignedState PS PB M :=
    { toFun := fun x => (x.2.1,x.2.2,x.1)
      invFun := fun s => (s.2.2,s.1,s.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let F (s : GiantSignedState PS PB M) :=
    (giantSignedStateMass PS ν s : ℂ) * star (f s) * g s
  have h : Summable (fun x : X => F (e x)) := hs.comp_injective e.injective
  change _ = ∑' s, F s
  rw [← e.tsum_eq F, h.tsum_prod]
  simp only [tsum_fintype, giantSignedStatePairing, giantSignedStateFiberPairing]
  rfl

theorem giantSignedStatePairing_self
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (f : GiantSignedState PS PB M → ℂ) (hf : giantSignedStateEnergy PS ν f ≠ ∞) :
    giantSignedStatePairing PS ν f f = (giantSignedStateEnergy PS ν f).toReal := by
  rw [giantSignedStatePairing_eq_tsum PS ν f f
    (giantSignedStatePairing_summable PS hVS ν hν f f hf hf),
    giantSignedStateEnergy_eq_tsum, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top),
    Complex.ofReal_tsum]
  apply tsum_congr
  intro s
  rw [ENNReal.toReal_ofReal (mul_nonneg (stateMass_nonneg PS hVS ν hν s) (sq_nonneg _)),
    Complex.ofReal_mul, mul_assoc, Complex.star_def,
    Complex.conj_mul', Complex.ofReal_pow]

theorem giantSignedStatePairing_energy
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (f g : GiantSignedState PS PB M → ℂ)
    (hf : giantSignedStateEnergy PS ν f ≠ ∞) (hg : giantSignedStateEnergy PS ν g ≠ ∞) :
    ENNReal.ofReal (‖giantSignedStatePairing PS ν f g‖ ^ 2) ≤
      giantSignedStateEnergy PS ν f * giantSignedStateEnergy PS ν g := by
  rw [giantSignedStatePairing_eq_tsum PS ν f g
    (giantSignedStatePairing_summable PS hVS ν hν f g hf hg)]
  simp only [giantSignedStateEnergy_eq_tsum] at hf hg ⊢
  exact giantSignedWeightedPairing_energy (giantSignedStateMass PS ν)
    (stateMass_nonneg PS hVS ν hν) f g hf hg

theorem giantSignedStateEnergy_le_of_pairing
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (g : GiantSignedState PS PB M → ℂ) (hg : giantSignedStateEnergy PS ν g ≠ ∞)
    (A : ℝ≥0∞)
    (h : ∀ f, giantSignedStateEnergy PS ν f ≠ ∞ →
      ENNReal.ofReal (‖giantSignedStatePairing PS ν f g‖ ^ 2) ≤
        A * giantSignedStateEnergy PS ν f) :
    giantSignedStateEnergy PS ν g ≤ A := by
  by_cases hz : giantSignedStateEnergy PS ν g = 0
  · rw [hz]
    exact zero_le
  have ht := h g hg
  rw [giantSignedStatePairing_self PS hVS ν hν g hg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hg, pow_two] at ht
  exact (ENNReal.mul_le_mul_iff_left hz hg).mp ht

end
end ArtinMatthews
