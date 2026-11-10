module

public import ArtinMatthews.GiantSignedConditionedPairing
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ordered-memory pairing is regrouped by its finite prime
and residue sectors using a derived equivalence and absolute convergence. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (j : B) (p : PB j), NeZero p.val]

def giantSignedConditionedSectorEquiv (k ell : ℕ) :
    GiantSignedConditionedIndex PS (PB := PB) k ell ≃
      Σ s : GiantSignedMemorySectors PB,
        MarkedPhysicalMarking PS k ×
          (GiantSignedResidueFiber PS s.2 × MarkedPhysicalMarking PB (k+ell)) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (giantSignedMemoryFiberEquiv PB) (Equiv.refl _))).trans
    { toFun := fun i => ⟨i.2.1.1, (i.1, ((i.2.2.1, i.2.1.2), i.2.2.2))⟩
      invFun := fun i => (i.2.1, (⟨i.1, i.2.2.1.2⟩, (i.2.2.1.1, i.2.2.2)))
      left_inv := by
        rintro ⟨d, ⟨⟨s, r⟩, y, a⟩⟩
        rfl
      right_inv := by
        rintro ⟨s, d, ⟨y, r⟩, a⟩
        rfl }

omit [Fintype B] [DecidableEq S] [DecidableEq B]
  [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
  [∀ (j : B) (p : PB j), NeZero p.val] in
theorem giantSignedConditionedSectorEquiv_symm_apply {k ell : ℕ}
    (s : GiantSignedMemorySectors PB) (d : MarkedPhysicalMarking PS k)
    (x : GiantSignedResidueFiber PS s.2) (a : MarkedPhysicalMarking PB (k+ell)) :
    (giantSignedConditionedSectorEquiv PS k ell).symm ⟨s, (d, (x, a))⟩ =
      (d, (giantSignedMemoryAt s x.2, (x.1, a))) := rfl

theorem giantSignedConditionedPairing_sector {k ell : ℕ}
    (ν : ∀ j, PB j → ℝ)
    (F G : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ)
    (hs : Summable (fun i : GiantSignedConditionedIndex PS (PB := PB) k ell =>
      (giantSignedConditionedWeight PS ν i : ℂ) *
        star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i)) :
    giantSignedConditionedPairing PS ν F G =
      ∑' s : GiantSignedMemorySectors PB, ∑ d : MarkedPhysicalMarking PS k,
        ∑ x : GiantSignedResidueFiber PS s.2, ∑ a : MarkedPhysicalMarking PB (k+ell),
          (giantSignedSmallHaar PS * giantSignedPrimeListMass ν s.2 * giantSignedActiveMass ν a : ℂ) *
            star (F d x.1 a (giantSignedMemoryAt s x.2)) *
            G d x.1 a (giantSignedMemoryAt s x.2) := by
  let f := fun i : GiantSignedConditionedIndex PS (PB := PB) k ell =>
    (giantSignedConditionedWeight PS ν i : ℂ) *
      star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i
  let e := giantSignedConditionedSectorEquiv (PB := PB) PS k ell
  have hse : Summable (fun j => f (e.symm j)) := hs.comp_injective e.symm.injective
  change (∑' i, f i) = _
  rw [← e.symm.tsum_eq f, hse.tsum_sigma]
  simp only [tsum_fintype, Fintype.sum_prod_type]
  apply tsum_congr
  intro s
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  dsimp only [f, e]
  rw [giantSignedConditionedSectorEquiv_symm_apply]
  simp only [giantSignedConditionedWeight, giantSignedConditionedValue, giantSignedMemoryAt_mass, Complex.ofReal_mul]

end
end ArtinMatthews
