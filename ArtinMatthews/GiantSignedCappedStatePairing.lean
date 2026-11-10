module

public import ArtinMatthews.GiantSignedStatePairingEnergy
public import ArtinMatthews.GiantSignedConditionedPairing
public import ArtinMatthews.GiantSignedStateMemoryCutoff
public import ArtinMatthews.GiantSignedCappedStateDomain
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

/-! Moving the actual memory projection to the left of the pairing
gives a finite support condition even after slot averaging and small
conditioning. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedStateMemoryCutoff_energy_ne_top (ν : ∀ g, PB g → ℝ) (N : ℕ)
    (f : GiantSignedState PS PB M → ℂ) :
    giantSignedStateEnergy PS ν (giantSignedStateMemoryCutoff N f) ≠ ∞ := by
  classical
  have hcap : ({s : GiantSignedState PS PB M | (∑ g, s.2.2.1 g) ≤ N} : Set _).Finite :=
    giantSignedCappedState_finite N
  rw [giantSignedStateEnergy_eq_tsum, tsum_eq_sum (s := hcap.toFinset)]
  · exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)
  · intro s hs
    have hdeg : N < ∑ g, s.2.2.1 g := by
      exact lt_of_not_ge (by simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hs)
    rw [giantSignedStateMemoryCutoff_of_lt N f s hdeg, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, ENNReal.ofReal_zero]

omit [∀ g, ∀ p : PB g, NeZero p.val] in
theorem giantSignedStatePairing_cutoff_right (ν : ∀ g, PB g → ℝ) (N : ℕ)
    (f g : GiantSignedState PS PB M → ℂ) :
    giantSignedStatePairing PS ν f (giantSignedStateMemoryCutoff N g) =
      giantSignedStatePairing PS ν (giantSignedStateMemoryCutoff N f) g := by
  unfold giantSignedStatePairing
  apply tsum_congr
  intro m
  unfold giantSignedStateFiberPairing
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : (∑ j, m.1 j) ≤ N <;> simp [giantSignedStateMemoryCutoff, h]

private theorem conditionedCap_finite (N : ℕ) :
    Finite {i : GiantSignedConditionedIndex PS (PB := PB) k ell // (∑ g, i.2.1.1 g) ≤ N} := by
  classical
  let X := {i : GiantSignedConditionedIndex PS (PB := PB) k ell // (∑ g, i.2.1.1 g) ≤ N}
  let Y := MarkedPhysicalMarking PS k ×
    ((Σ d : B → Fin (N+1), ∀ g, Fin (d g).val → GiantSignedParticle (PB g)) ×
      (GiantTwoSidedFullResidue PS × MarkedPhysicalMarking PB (k+ell)))
  letI : Fintype Y := by dsimp [Y]; infer_instance
  have hdeg (x : X) (g : B) : x.1.2.1.1 g < N+1 :=
    Nat.lt_succ_of_le ((Finset.single_le_sum (f := x.1.2.1.1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)).trans x.2)
  let enc (x : X) : Y :=
    (x.1.1, ⟨fun g => ⟨x.1.2.1.1 g, hdeg x g⟩, x.1.2.1.2⟩, x.1.2.2)
  let dec (y : Y) : GiantSignedConditionedIndex PS (PB := PB) k ell :=
    (y.1, ⟨fun g => (y.2.1.1 g).val, y.2.1.2⟩, y.2.2)
  refine Finite.of_injective enc ?_
  intro x y he
  exact Subtype.ext (congrArg dec he)

omit [∀ g, ∀ p : PB g, NeZero p.val] in
private theorem smallConditioning_slotCutoff_zero
    (N : ℕ) (q : ℝ) (f : GiantSignedState PS PB (k+ell) → ℂ)
    (d : MarkedPhysicalMarking PS k) (y : GiantTwoSidedFullResidue PS)
    (a : MarkedPhysicalMarking PB (k+ell)) (m : GiantSignedMemory PB)
    (h : N < ∑ g, m.1 g) :
    giantSignedSmallConditioning PS q d
      (giantSignedStateSlotAverage PS (giantSignedStateMemoryCutoff N f)) y a m = 0 := by
  have hz (s : GiantTwoSidedResidueState PS (k+ell)) :
      giantSignedStateSlotAverage PS (giantSignedStateMemoryCutoff N f) (s,a,m) = 0 := by
    unfold giantSignedStateSlotAverage
    apply Finset.sum_eq_zero
    intro π _
    rw [giantSignedStateMemoryCutoff_of_lt N _ _ h, mul_zero]
  unfold giantSignedSmallConditioning giantSmallConditioningMap
  have ht (r : MarkedPhysicalMarking PS ell) :
      giantSmallStateValue
        (fun s => giantSignedStateSlotAverage PS (giantSignedStateMemoryCutoff N f) (s,a,m))
        y (giantSmallAppend d r) = 0 := by
    unfold giantSmallStateValue
    split_ifs with hs
    · exact hz _
    · rfl
  simp only [ht, Finset.sum_const_zero, mul_zero]

theorem giantSignedConditionedPairing_slotCutoff_summable
    (ν : ∀ g, PB g → ℝ) (N : ℕ) (q : ℝ) (f : GiantSignedState PS PB (k+ell) → ℂ)
    (G : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ) :
    let F := fun d => giantSignedSmallConditioning PS q d
      (giantSignedStateSlotAverage PS (giantSignedStateMemoryCutoff N f))
    Summable (fun i : GiantSignedConditionedIndex PS (PB := PB) k ell =>
      (giantSignedConditionedWeight PS ν i : ℂ) *
        star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i) := by
  dsimp only
  classical
  let X := GiantSignedConditionedIndex PS (PB := PB) k ell
  have hcap : ({i : X | (∑ g, i.2.1.1 g) ≤ N} : Set X).Finite :=
    conditionedCap_finite PS N
  apply summable_of_hasFiniteSupport
  apply hcap.subset
  intro i hi
  change (∑ g, i.2.1.1 g) ≤ N
  by_contra! h
  have hz := smallConditioning_slotCutoff_zero PS N q f i.1 i.2.2.1 i.2.2.2 i.2.1 h
  apply hi
  simp only [giantSignedConditionedValue, hz, star_zero, mul_zero, zero_mul]

end
end ArtinMatthews
