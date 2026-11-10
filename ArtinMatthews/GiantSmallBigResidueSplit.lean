module

public import ArtinMatthews.GiantFullPrimeLifespan
public import ArtinMatthews.GiantTwoSidedResiduePrimeFactor
public import ArtinMatthews.GiantTwoSidedResidueRootSum
public import ArtinMatthews.GiantFullPrimeSource
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

/-!
# The actual small/big residue split

Restricting the original marking array to the two summands preserves every
slot. Disjoint prime unions separate the literal small residue average from
the finite big-prime lifespan sum.
-/

namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B]
variable {PS : S → Finset ℕ} {PB : B → Finset ℕ}

def giantSignedSmallMarking {M n : ℕ}
    (labels : Fin (n + 1) → MarkedPhysicalMarking (Sum.elim PS PB) M) :
    Fin (n + 1) → MarkedPhysicalMarking PS M :=
  fun i s k => labels i (Sum.inl s) k

def giantSignedBigMarking {M n : ℕ}
    (labels : Fin (n + 1) → MarkedPhysicalMarking (Sum.elim PS PB) M) :
    Fin (n + 1) → MarkedPhysicalMarking PB M :=
  fun i b k => labels i (Sum.inr b) k

theorem giantSignedSplitBandPrimes (PS : S → Finset ℕ) (PB : B → Finset ℕ) :
    markedPhysicalBandPrimes (Sum.elim PS PB) =
      markedPhysicalBandPrimes PS ∪ markedPhysicalBandPrimes PB := by
  ext p
  simp only [markedPhysicalBandPrimes, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_union]
  constructor
  · rintro ⟨g, hg⟩
    cases g with
    | inl s => exact Or.inl ⟨s, hg⟩
    | inr b => exact Or.inr ⟨b, hg⟩
  · rintro (⟨s, hs⟩ | ⟨b, hb⟩)
    · exact ⟨Sum.inl s, hs⟩
    · exact ⟨Sum.inr b, hb⟩

theorem giantSignedSmallActiveVisits {M n : ℕ}
    (labels : Fin (n + 1) → MarkedPhysicalMarking (Sum.elim PS PB) M)
    (hdis : Disjoint (markedPhysicalBandPrimes PS) (markedPhysicalBandPrimes PB))
    {p : ℕ} (hp : p ∈ markedPhysicalBandPrimes PS) :
    giantSignedActualActiveVisits labels p =
      giantSignedActualActiveVisits (giantSignedSmallMarking labels) p := by
  ext i
  simp only [mem_giantSignedActualActiveVisits]
  constructor
  · rintro ⟨g, k, hg⟩
    cases g with
    | inl s => exact ⟨s, k, hg⟩
    | inr b =>
      have hpB : p ∈ markedPhysicalBandPrimes PB :=
        Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, hg ▸ (labels i (Sum.inr b) k).property⟩
      exact (Finset.disjoint_left.mp hdis hp hpB).elim
  · rintro ⟨s, k, hs⟩
    exact ⟨Sum.inl s, k, hs⟩

theorem giantSignedBigActiveVisits {M n : ℕ}
    (labels : Fin (n + 1) → MarkedPhysicalMarking (Sum.elim PS PB) M)
    (hdis : Disjoint (markedPhysicalBandPrimes PS) (markedPhysicalBandPrimes PB))
    {p : ℕ} (hp : p ∈ markedPhysicalBandPrimes PB) :
    giantSignedActualActiveVisits labels p =
      giantSignedActualActiveVisits (giantSignedBigMarking labels) p := by
  ext i
  simp only [mem_giantSignedActualActiveVisits]
  constructor
  · rintro ⟨g, k, hg⟩
    cases g with
    | inl s =>
      have hpS : p ∈ markedPhysicalBandPrimes PS :=
        Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ s, hg ▸ (labels i (Sum.inl s) k).property⟩
      exact (Finset.disjoint_left.mp hdis hpS hp).elim
    | inr b => exact ⟨b, k, hg⟩
  · rintro ⟨b, k, hb⟩
    exact ⟨Sum.inr b, k, hb⟩

/-- Numeric prime means provide the common product indexing for both summands. -/
theorem giantSignedPrimeResidueExpectation_eq_primeMean {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking P M)
    (offset : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ) (p : ℕ) [NeZero p] :
    giantSignedPrimeResidueExpectation p offset q (giantSignedActualActiveVisits labels p) =
      giantTwoSidedIndependentPrimeMean labels q offset p := by
  rw [giantTwoSidedIndependentPrimeMean_eq]
  simp_rw [giantSignedExistingPrimeFactor_eq]
  unfold giantSignedPrimeResidueExpectation
  simp only [div_eq_mul_inv, one_mul]
  exact mul_comm _ _

theorem giantSignedFullPrimeResidueMean_numeric_product {J : Type*} [Fintype J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val] {M n : ℕ}
    (labels : Fin (n + 1) → MarkedPhysicalMarking P M)
    (offset : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ) :
    giantSignedFullPrimeResidueMean labels offset q =
      ∏ p ∈ markedPhysicalBandPrimes P, giantTwoSidedIndependentPrimeMean labels q offset p := by
  rw [giantSignedFullPrimeResidueMean_product]
  simp_rw [giantSignedPrimeResidueExpectation_eq_primeMean labels offset q]
  exact Finset.prod_coe_sort _ _

/-- The literal small and big means multiply when their prime unions are disjoint. -/
theorem giantSignedFullPrimeResidueMean_small_big
    [hS : ∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [hB : ∀ p : ↥(markedPhysicalBandPrimes PB), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes (Sum.elim PS PB)), NeZero p.val]
    {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking (Sum.elim PS PB) M)
    (offset : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ)
    (hdis : Disjoint (markedPhysicalBandPrimes PS) (markedPhysicalBandPrimes PB)) :
    giantSignedFullPrimeResidueMean labels offset q =
      giantSignedFullPrimeResidueMean (giantSignedSmallMarking labels) offset q *
        giantSignedFullPrimeResidueMean (giantSignedBigMarking labels) offset q := by
  rw [giantSignedFullPrimeResidueMean_numeric_product labels offset q,
    giantSignedFullPrimeResidueMean_numeric_product (giantSignedSmallMarking labels) offset q,
    giantSignedFullPrimeResidueMean_numeric_product (giantSignedBigMarking labels) offset q,
    giantSignedSplitBandPrimes, Finset.prod_union hdis]
  apply congrArg₂ (fun x y : ℝ => x * y)
  · apply Finset.prod_congr rfl
    intro p hp
    let : NeZero p := hS ⟨p, hp⟩
    rw [← giantSignedPrimeResidueExpectation_eq_primeMean labels offset q p,
      ← giantSignedPrimeResidueExpectation_eq_primeMean (giantSignedSmallMarking labels) offset q p,
      giantSignedSmallActiveVisits labels hdis hp]
  · apply Finset.prod_congr rfl
    intro p hp
    let : NeZero p := hB ⟨p, hp⟩
    rw [← giantSignedPrimeResidueExpectation_eq_primeMean labels offset q p,
      ← giantSignedPrimeResidueExpectation_eq_primeMean (giantSignedBigMarking labels) offset q p,
      giantSignedBigActiveVisits labels hdis hp]

/-- Groupwise disjointness gives the disjoint small and big prime unions. -/
theorem giantSignedSmallBigPrimes_disjoint
    (hdis : Pairwise (fun i j : Sum S B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j))) :
    Disjoint (markedPhysicalBandPrimes PS) (markedPhysicalBandPrimes PB) := by
  apply Finset.disjoint_left.mpr
  intro p hpS hpB
  obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp hpS
  obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp hpB
  exact Finset.disjoint_left.mp (hdis (Sum.inl_ne_inr : Sum.inl s ≠ Sum.inr b)) hs hb

/-- The small factor stays as its literal finite residue mean while the big
factor uses the exact normalized lifespan family. -/
theorem giantSignedFullPrimeResidueMean_small_big_lifespans
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes PB), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes (Sum.elim PS PB)), NeZero p.val]
    {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking (Sum.elim PS PB) M)
    (offset : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ)
    (hdis : Disjoint (markedPhysicalBandPrimes PS) (markedPhysicalBandPrimes PB))
    (hb : ∀ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeResidueBaseline p.val q ≠ 0) :
    giantSignedFullPrimeResidueMean labels offset q =
      giantSignedFullPrimeResidueMean (giantSignedSmallMarking labels) offset q *
        (∏ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeResidueBaseline p.val q) *
        ∑ c : GiantSignedFullPrimeLifespanChoice (giantSignedBigMarking labels),
          ∏ p : ↥(markedPhysicalBandPrimes PB),
            giantSignedResidueLifespanWeight p.val offset q
              (giantSignedActualActiveVisits (giantSignedBigMarking labels) p.val) (c p) /
                giantSignedPrimeResidueBaseline p.val q := by
  rw [giantSignedFullPrimeResidueMean_small_big labels offset q hdis,
    giantSignedFullPrimeResidueMean_baselines (giantSignedBigMarking labels) offset q hb]
  simp only [mul_assoc]

/-- The actual source mean retains the small Haar average and expands
only the big-prime factor at its original visit schedule. -/
theorem giantSignedSourceResidueMean_small_big_lifespans
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes PB), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes (Sum.elim PS PB)), NeZero p.val]
    {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking (Sum.elim PS PB) M)
    (offset : Fin (n + 1) → ℤ) (q : ℝ)
    (hdis : Pairwise (fun i j : Sum S B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hb : ∀ p : ↥(markedPhysicalBandPrimes PB),
      giantSignedPrimeResidueBaseline p.val (markedMemoryVisitQ q n) ≠ 0) :
    giantTwoSidedIndependentResidueMean labels q offset =
      giantSignedFullPrimeResidueMean (giantSignedSmallMarking labels) offset (markedMemoryVisitQ q n) *
        (∏ p : ↥(markedPhysicalBandPrimes PB),
          giantSignedPrimeResidueBaseline p.val (markedMemoryVisitQ q n)) *
        ∑ c : GiantSignedFullPrimeLifespanChoice (giantSignedBigMarking labels),
          ∏ p : ↥(markedPhysicalBandPrimes PB),
            giantSignedResidueLifespanWeight p.val offset (markedMemoryVisitQ q n)
              (giantSignedActualActiveVisits (giantSignedBigMarking labels) p.val) (c p) /
                giantSignedPrimeResidueBaseline p.val (markedMemoryVisitQ q n) := by
  rw [← giantSignedFullPrimeResidueMean_eq_source hdis labels offset q]
  exact giantSignedFullPrimeResidueMean_small_big_lifespans labels offset _
    (giantSignedSmallBigPrimes_disjoint hdis) hb

end
end ArtinMatthews
