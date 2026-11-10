module

public import ArtinMatthews.GiantSignedJoinedBigLifespan
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

/-! The literal small-residue and big-lifespan split on the support of the grouped choices. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] {PS : S → Finset ℕ} {PB : B → Finset ℕ}
    {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking (Sum.elim PS PB) M)
    (hdis : Pairwise (fun g h : Sum S B => Disjoint (Sum.elim PS PB g) (Sum.elim PS PB h)))
    (offset : Fin (n+1) → ℤ) (q : Fin (n+1) → ℝ)

def GiantSignedJoinedBigLifespanSupported (c : GiantSignedJoinedBigLifespanChoice labels) : Prop :=
  ∀ g (p : PB g), giantSignedResidueLifespanWeight p.val offset q
    (giantSignedActualActiveVisits labels p.val) (c g p) ≠ 0

theorem giantSignedJoinedBigLifespanEquiv_supported_iff
    (c : GiantSignedFullPrimeLifespanChoice (giantSignedBigMarking labels)) :
    GiantSignedJoinedBigLifespanSupported labels offset q (giantSignedJoinedBigLifespanEquiv labels hdis c) ↔
      ∀ p : ↥(markedPhysicalBandPrimes PB), giantSignedResidueLifespanWeight p.val offset q
        (giantSignedActualActiveVisits (giantSignedBigMarking labels) p.val) (c p) ≠ 0 := by
  constructor
  · intro hc p
    obtain ⟨g, _, hg⟩ := Finset.mem_biUnion.mp p.property
    let t : PB g := ⟨p.val, hg⟩
    have he : giantTwoSidedResidueIndex g t = p := Subtype.ext rfl
    have hz := hc g t
    rw [giantSignedJoinedBigLifespanEquiv_weight labels hdis] at hz
    let keep (a : ↥(markedPhysicalBandPrimes PB)) := giantSignedResidueLifespanWeight a.val offset q
      (giantSignedActualActiveVisits (giantSignedBigMarking labels) a.val) (c a) ≠ 0
    exact (congrArg keep he).mp (show keep (giantTwoSidedResidueIndex g t) from hz)
  · intro hc g p
    rw [giantSignedJoinedBigLifespanEquiv_weight labels hdis]
    exact hc (giantTwoSidedResidueIndex g p)

def giantSignedJoinedBigLifespanSupportedEquiv :
    {c : GiantSignedFullPrimeLifespanChoice (giantSignedBigMarking labels) //
      ∀ p : ↥(markedPhysicalBandPrimes PB), giantSignedResidueLifespanWeight p.val offset q
        (giantSignedActualActiveVisits (giantSignedBigMarking labels) p.val) (c p) ≠ 0} ≃
      {c : GiantSignedJoinedBigLifespanChoice labels // GiantSignedJoinedBigLifespanSupported labels offset q c} :=
  (giantSignedJoinedBigLifespanEquiv labels hdis).subtypeEquiv fun c =>
    (giantSignedJoinedBigLifespanEquiv_supported_iff labels hdis offset q c).symm

private theorem unsupported_product_zero (c : GiantSignedJoinedBigLifespanChoice labels)
    (h : ¬GiantSignedJoinedBigLifespanSupported labels offset q c) :
    giantSignedJoinedBigLifespanNormalizedProduct labels offset q c = 0 := by
  have he : ∃ (g : B) (p : PB g), giantSignedResidueLifespanWeight p.val offset q
      (giantSignedActualActiveVisits labels p.val) (c g p) = 0 := by
    by_contra hn
    exact h (fun g p hz => hn ⟨g, p, hz⟩)
  obtain ⟨g, p, hz⟩ := he
  unfold giantSignedJoinedBigLifespanNormalizedProduct
  exact Finset.prod_eq_zero (Finset.mem_univ g)
    (Finset.prod_eq_zero (Finset.mem_univ p) (by rw [hz, zero_div]))

theorem giantSignedJoinedBigLifespanNormalizedProduct_ne_zero_iff
    (c : GiantSignedJoinedBigLifespanChoice labels)
    (hb : ∀ g (p : PB g), giantSignedPrimeResidueBaseline p.val q ≠ 0) :
    giantSignedJoinedBigLifespanNormalizedProduct labels offset q c ≠ 0 ↔
      GiantSignedJoinedBigLifespanSupported labels offset q c := by
  constructor
  · exact fun hn => by_contra fun hs => hn (unsupported_product_zero labels offset q c hs)
  · intro hs
    exact Finset.prod_ne_zero_iff.mpr (fun g _ =>
      Finset.prod_ne_zero_iff.mpr (fun p _ => div_ne_zero (hs g p) (hb g p)))

include hdis in
theorem giantSignedJoinedBigLifespan_sum_supported :
    (∑ c : GiantSignedFullPrimeLifespanChoice (giantSignedBigMarking labels),
      ∏ p : ↥(markedPhysicalBandPrimes PB), giantSignedResidueLifespanWeight p.val offset q
        (giantSignedActualActiveVisits (giantSignedBigMarking labels) p.val) (c p) /
          giantSignedPrimeResidueBaseline p.val q) =
      ∑ c : {c : GiantSignedJoinedBigLifespanChoice labels //
        GiantSignedJoinedBigLifespanSupported labels offset q c},
          giantSignedJoinedBigLifespanNormalizedProduct labels offset q c.val := by
  let norm := giantSignedJoinedBigLifespanNormalizedProduct labels offset q
  let supported := GiantSignedJoinedBigLifespanSupported labels offset q
  calc
    _ = ∑ c : GiantSignedJoinedBigLifespanChoice labels, norm c := by
      rw [← (giantSignedJoinedBigLifespanEquiv labels hdis).sum_comp norm]
      exact Finset.sum_congr rfl fun c _ =>
        (giantSignedJoinedBigLifespanEquiv_normalizedProduct labels hdis offset q c).symm
    _ = _ := by
      have hs := Finset.sum_subtype (p := supported) (F := inferInstance)
        (Finset.univ.filter supported) (by simp) norm
      rw [← hs, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : supported c
      · rw [ite_eq_left hc]
      · rw [ite_eq_right hc]
        exact unsupported_product_zero labels offset q c hc

include hdis in
theorem giantSignedSourceResidueMean_small_big_supported
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes PB), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes (Sum.elim PS PB)), NeZero p.val]
    (q₀ : ℝ)
    (hb : ∀ p : ↥(markedPhysicalBandPrimes PB),
      giantSignedPrimeResidueBaseline p.val (markedMemoryVisitQ q₀ n) ≠ 0) :
    giantTwoSidedIndependentResidueMean labels q₀ offset =
      giantSignedFullPrimeResidueMean (giantSignedSmallMarking labels) offset (markedMemoryVisitQ q₀ n) *
        (∏ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeResidueBaseline p.val (markedMemoryVisitQ q₀ n)) *
        ∑ c : {c : GiantSignedJoinedBigLifespanChoice labels //
          GiantSignedJoinedBigLifespanSupported labels offset (markedMemoryVisitQ q₀ n) c},
            giantSignedJoinedBigLifespanNormalizedProduct labels offset (markedMemoryVisitQ q₀ n) c.val := by
  rw [giantSignedSourceResidueMean_small_big_lifespans labels offset q₀ hdis hb,
    giantSignedJoinedBigLifespan_sum_supported labels hdis offset (markedMemoryVisitQ q₀ n)]

end
end ArtinMatthews
