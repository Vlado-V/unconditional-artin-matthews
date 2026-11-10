module

public import ArtinMatthews.GiantSignedConditioningEnergy
public import ArtinMatthews.GiantSignedStatePermutationEnergy
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

/-! Finite path terms are added in the original state energy. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedStateEnergy_sum_le {I : Type*} [Fintype I]
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (f : I → GiantSignedState PS PB M → ℂ) :
    giantSignedStateEnergy PS ν (fun s => ∑ i, f i s) ≤
      (Fintype.card I : ℝ≥0∞) * ∑ i, giantSignedStateEnergy PS ν (f i) := by
  classical
  have hmass (s : GiantSignedState PS PB M) : 0 ≤ giantSignedStateMass PS ν s := by
    apply mul_nonneg
    · apply mul_nonneg
      · unfold giantTwoSidedResidueHaarStateMass markedPhysicalMass
        exact div_nonneg
          (Finset.prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _)
          (Nat.cast_nonneg _)
      · exact Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ => hν g _
    · exact giantSignedMemoryMass_nonneg ν hν s.2.2
  have hpoint (s : GiantSignedState PS PB M) :
      ENNReal.ofReal (giantSignedStateMass PS ν s * ‖∑ i, f i s‖ ^ 2) ≤
        (Fintype.card I : ℝ≥0∞) *
          ∑ i, ENNReal.ofReal (giantSignedStateMass PS ν s * ‖f i s‖ ^ 2) := by
    have hsq : ‖∑ i, f i s‖ ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, ‖f i s‖ ^ 2 := by
      calc
        _ ≤ (∑ i, ‖f i s‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
        _ ≤ _ := by simpa only [Finset.card_univ] using
          (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖f i s‖))
    apply (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsq (hmass s))).trans_eq
    have he : giantSignedStateMass PS ν s * ((Fintype.card I : ℝ) * ∑ i, ‖f i s‖ ^ 2) =
        (Fintype.card I : ℝ) * ∑ i, giantSignedStateMass PS ν s * ‖f i s‖ ^ 2 := by
      rw [← Finset.mul_sum]
      ring
    rw [he, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => mul_nonneg (hmass s) (sq_nonneg _))]
  rw [giantSignedStateEnergy_eq_tsum]
  calc
    _ ≤ ∑' s : GiantSignedState PS PB M, (Fintype.card I : ℝ≥0∞) *
        ∑ i, ENNReal.ofReal (giantSignedStateMass PS ν s * ‖f i s‖ ^ 2) :=
      ENNReal.tsum_le_tsum hpoint
    _ = (Fintype.card I : ℝ≥0∞) *
        ∑' s : GiantSignedState PS PB M, ∑' i : I,
          ENNReal.ofReal (giantSignedStateMass PS ν s * ‖f i s‖ ^ 2) := by
      simp only [tsum_fintype, ENNReal.tsum_mul_left]
    _ = (Fintype.card I : ℝ≥0∞) *
        ∑' i : I, ∑' s : GiantSignedState PS PB M,
          ENNReal.ofReal (giantSignedStateMass PS ν s * ‖f i s‖ ^ 2) := by
      rw [ENNReal.tsum_comm]
    _ = _ := by simp only [tsum_fintype, giantSignedStateEnergy_eq_tsum]

theorem giantSignedStateEnergy_sum_le_card_sq {I : Type*} [Fintype I]
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (f : I → GiantSignedState PS PB M → ℂ) (A : ℝ≥0∞)
    (hf : ∀ i, giantSignedStateEnergy PS ν (f i) ≤ A) :
    giantSignedStateEnergy PS ν (fun s => ∑ i, f i s) ≤
      (Fintype.card I : ℝ≥0∞) ^ 2 * A := by
  refine (giantSignedStateEnergy_sum_le PS hV ν hν f).trans ?_
  calc
    _ ≤ (Fintype.card I : ℝ≥0∞) * ∑ _i : I, A :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hf i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end
end ArtinMatthews
