module

public import ArtinMatthews.GiantSignedCleanDisintegration
public import ArtinMatthews.GiantTwoSidedResidueInitialMass
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

/-! The empty-memory boundary leaves both endpoint active lists free. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedActiveMass_sum {B : Type*} [Fintype B] [DecidableEq B]
    {P : B → Finset ℕ} (ν : ∀ g, P g → ℝ) (M : ℕ) :
    (∑ a : MarkedPhysicalMarking P M, giantSignedActiveMass ν a) =
      ∏ g, (∑ p : P g, ν g p) ^ M := by
  classical
  unfold giantSignedActiveMass
  rw [← Fintype.prod_sum (fun g (a : Fin M → P g) => ∏ i, ν g (a i))]
  apply Finset.prod_congr rfl
  intro g _
  exact (Fintype.sum_pow (ν g) M).symm

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

def giantSignedBoundaryEnergy (ν : ∀ g, PB g → ℝ) (M : ℕ) : ℝ≥0∞ :=
  ∑' m : GiantSignedMemory PB, ∑ s : GiantTwoSidedResidueState PS M,
    ∑ a : MarkedPhysicalMarking PB M,
      ENNReal.ofReal (giantSignedStateMass PS ν (s, a, m) *
        ‖giantSignedBoundary (s, a, m)‖ ^ 2)

theorem giantSignedBoundaryEnergy_eq (ν : ∀ g, PB g → ℝ)
    (hν : ∀ g p, 0 ≤ ν g p) (hV : ∀ g, 0 < bandReciprocalMass (PS g)) (M : ℕ) :
    giantSignedBoundaryEnergy PS ν M =
      ENNReal.ofReal ((∑ _s : GiantTwoSidedResidueState PS M,
        giantTwoSidedResidueHaarStateMass PS M) * ∏ g, (∑ p : PB g, ν g p) ^ M) := by
  classical
  have hs : 0 ≤ giantTwoSidedResidueHaarStateMass PS M := by
    unfold giantTwoSidedResidueHaarStateMass markedPhysicalMass
    exact div_nonneg (Finset.prod_nonneg fun g _ => pow_nonneg (inv_nonneg.mpr (hV g).le) _)
      (Nat.cast_nonneg _)
  have ha (a : MarkedPhysicalMarking PB M) : 0 ≤ giantSignedActiveMass ν a :=
    Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ => hν g (a g i)
  unfold giantSignedBoundaryEnergy
  rw [tsum_eq_single (giantSignedEmptyMemory PB)]
  · simp only [giantSignedBoundary_empty, norm_one, one_pow, mul_one, giantSignedStateMass,
      giantSignedEmptyMemory_mass]
    rw [← giantSignedActiveMass_sum ν M, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
      Finset.sum_nonneg fun a _ => mul_nonneg hs (ha a))]
    apply Finset.sum_congr rfl
    intro s _
    exact (ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg hs (ha a))).symm
  · intro m hm
    simp only [giantSignedBoundary, hm, ite_false, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, ENNReal.ofReal_zero, Finset.sum_const_zero]

theorem giantSignedBoundaryEnergy_le (ν : ∀ g, PB g → ℝ)
    (hν : ∀ g p, 0 ≤ ν g p) (hP : ∀ g p, p ∈ PS g → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hV : ∀ g, 0 < bandReciprocalMass (PS g)) (M : ℕ) :
    giantSignedBoundaryEnergy PS ν M ≤
      ENNReal.ofReal (∏ g, (∑ p : PB g, ν g p) ^ M) := by
  rw [giantSignedBoundaryEnergy_eq PS ν hν hV]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_of_le_one_left
    (Finset.prod_nonneg fun g _ => pow_nonneg (Finset.sum_nonneg fun p _ => hν g p) _)
    (giantTwoSidedResidue_initialMass_le_one PS hP hdis hV M)

end
end ArtinMatthews
