module

public import ArtinMatthews.GiantFullPrimeMean
public import ArtinMatthews.GiantTwoSidedResiduePrimeFactor
public import ArtinMatthews.GiantTwoSidedResidueRootSum
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The full-prime scalar identity specializes to the existing actual
signed-path residue mean with its square-root endpoint visit schedule. -/

namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The existing literal prime factor is the active indicator times the
unmarked hit damping product. -/
theorem giantSignedExistingPrimeFactor_eq {J : Type*} [Fintype J] {PB : J → Finset ℕ}
    {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking PB M)
    (offset : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ) (p : ℕ) (r : ZMod p) :
    giantTwoSidedIndependentPrimeFactor labels q offset p r =
      (if ∀ i ∈ giantSignedActualActiveVisits labels p, r + (offset i : ZMod p) = 0
        then 1 else 0) *
        ∏ i ∈ Finset.univ \ giantSignedActualActiveVisits labels p,
          (1 - (1 - q i) * giantSignedPrimeResidueHit p offset i r) := by
  let A := giantSignedActualActiveVisits labels p
  have ha : (∏ i ∈ A, if r + (offset i : ZMod p) = 0 then (1 : ℝ) else 0) =
      if ∀ i ∈ A, r + (offset i : ZMod p) = 0 then 1 else 0 := by
    by_cases h : ∀ i ∈ A, r + (offset i : ZMod p) = 0
    · rw [ite_eq_left h]
      exact Finset.prod_eq_one (fun i hi => ite_eq_left (h i hi))
    · obtain ⟨i, hi, hmiss⟩ : ∃ i ∈ A, r + (offset i : ZMod p) ≠ 0 := by
        simpa only [not_forall, exists_prop] using h
      rw [ite_eq_right h]
      exact Finset.prod_eq_zero hi (ite_eq_right hmiss)
  have hn : (Finset.univ : Finset (Fin (n + 1))).filter
      (fun i => p ∉ markedPhysicalActivePrimes (labels i)) = Finset.univ \ A := by
    ext i
    simp [A, giantSignedActualActiveVisits]
  unfold giantTwoSidedIndependentPrimeFactor
  rw [Finset.prod_ite]
  change (∏ i ∈ A, if r + (offset i : ZMod p) = 0 then (1 : ℝ) else 0) * _ = _
  rw [ha, hn]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  by_cases hh : r + (offset i : ZMod p) = 0 <;>
    simp [giantSignedPrimeResidueHit, hh]

/-- The new arbitrary-weight full tuple factor agrees with the existing
source factor at the actual endpoint/interior visit schedule. -/
theorem giantSignedFullPrimeResidueFactor_eq_source {J : Type*} [Fintype J]
    {PB : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (PB i) (PB j)))
    {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking PB M)
    (offset : Fin (n + 1) → ℤ) (q : ℝ) (root : GiantTwoSidedFullResidue PB) :
    giantSignedFullPrimeResidueFactor labels offset (markedMemoryVisitQ q n) root =
      giantTwoSidedIndependentResidueFactor PB labels q offset root := by
  rw [giantTwoSidedIndependentResidueFactor_product hdis,
    giantSignedFullPrimeResidueFactor_product]
  apply Finset.prod_congr rfl
  intro p _
  exact (giantSignedExistingPrimeFactor_eq labels offset _ p.val (root p)).symm

/-- Literal Haar normalization is the existing full-residue cardinality. -/
theorem giantSignedFullPrimeResidueMean_eq_source {J : Type*} [Fintype J]
    {PB : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes PB), NeZero p.val]
    (hdis : Pairwise (fun i j => Disjoint (PB i) (PB j))) {M n : ℕ}
    (labels : Fin (n + 1) → MarkedPhysicalMarking PB M)
    (offset : Fin (n + 1) → ℤ) (q : ℝ) :
    giantSignedFullPrimeResidueMean labels offset (markedMemoryVisitQ q n) =
      giantTwoSidedIndependentResidueMean labels q offset := by
  unfold giantSignedFullPrimeResidueMean giantTwoSidedIndependentResidueMean
  simp_rw [giantSignedFullPrimeResidueFactor_eq_source hdis]
  congr 1
  simp only [GiantTwoSidedFullResidue, Fintype.card_pi, ZMod.card, Nat.cast_prod]

end
end ArtinMatthews
