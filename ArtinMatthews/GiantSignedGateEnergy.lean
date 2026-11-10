module

public import ArtinMatthews.GiantSignedConditioningEnergy
public import ArtinMatthews.GiantSignedStatePermutationEnergy
public import ArtinMatthews.WeightedGateCauchySchwarz
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

/-! Gate mass is converted into energy gain in the original full-state law. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedStateEnergy_gate_average {I : Type*} [Fintype I]
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (gate : GiantSignedState PS PB M → I → Prop)
    (F : I → GiantSignedState PS PB M → ℂ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hmass : ∀ s, (∑ i, if gate s i then w i else 0) ≤ ε) :
    giantSignedStateEnergy PS ν (fun s => ∑ i, (w i : ℂ) * (if gate s i then F i s else 0)) ≤
      ENNReal.ofReal ε * ∑ i, ENNReal.ofReal (w i) * giantSignedStateEnergy PS ν (F i) := by
  have hstate (s : GiantSignedState PS PB M) : 0 ≤ giantSignedStateMass PS ν s := by
    apply mul_nonneg
    · apply mul_nonneg
      · unfold giantTwoSidedResidueHaarStateMass markedPhysicalMass
        exact div_nonneg
          (Finset.prod_nonneg (fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _))
          (Nat.cast_nonneg _)
      · exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hν g _))
    · exact giantSignedMemoryMass_nonneg ν hν s.2.2
  have hpoint (s : GiantSignedState PS PB M) :
      ENNReal.ofReal (giantSignedStateMass PS ν s *
        ‖∑ i, (w i : ℂ) * (if gate s i then F i s else 0)‖ ^ 2) ≤
      ENNReal.ofReal ε * ∑ i, ENNReal.ofReal (w i) *
        ENNReal.ofReal (giantSignedStateMass PS ν s * ‖F i s‖ ^ 2) := by
    have hg := weightedGate_norm_sq_le w hw (gate s) (fun i => F i s) ε (hmass s)
    apply (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hg (hstate s))).trans_eq
    rw [mul_left_comm, ENNReal.ofReal_mul hε, Finset.mul_sum,
      ENNReal.ofReal_sum_of_nonneg
        (fun i _ => mul_nonneg (hstate s) (mul_nonneg (hw i) (sq_nonneg _)))]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← ENNReal.ofReal_mul (hw i)]
    congr 1
    ring
  rw [giantSignedStateEnergy_eq_tsum]
  calc
    _ ≤ ∑' s : GiantSignedState PS PB M, ENNReal.ofReal ε * ∑ i,
        ENNReal.ofReal (w i) * ENNReal.ofReal (giantSignedStateMass PS ν s * ‖F i s‖ ^ 2) :=
      ENNReal.tsum_le_tsum hpoint
    _ = ENNReal.ofReal ε * ∑' s : GiantSignedState PS PB M, ∑ i,
        ENNReal.ofReal (w i) * ENNReal.ofReal (giantSignedStateMass PS ν s * ‖F i s‖ ^ 2) := by
      rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal ε * ∑' s : GiantSignedState PS PB M, ∑' i : I,
        ENNReal.ofReal (w i) * ENNReal.ofReal (giantSignedStateMass PS ν s * ‖F i s‖ ^ 2) := by
      simp only [tsum_fintype]
    _ = ENNReal.ofReal ε * ∑' i : I, ∑' s : GiantSignedState PS PB M,
        ENNReal.ofReal (w i) * ENNReal.ofReal (giantSignedStateMass PS ν s * ‖F i s‖ ^ 2) := by
      rw [ENNReal.tsum_comm]
    _ = _ := by
      simp only [tsum_fintype, ENNReal.tsum_mul_left, giantSignedStateEnergy_eq_tsum]

end
end ArtinMatthews
