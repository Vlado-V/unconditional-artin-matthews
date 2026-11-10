module

public import ArtinMatthews.GiantSignedFixedLifespanSourceWeight
public import ArtinMatthews.GiantSignedLifespanOriginalPathFinite
public import ArtinMatthews.GiantSignedCappedBoundaryRank
public import ArtinMatthews.GiantSignedTiltedLaw
public import ArtinMatthews.GiantSignedAdmissibleTraceOrderedSum
public import ArtinMatthews.GiantSignedFixedLifespanPointwise
public import ArtinMatthews.GiantSignedLifespanOrderSum
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

/-! The actual uncapped distinct-birth trace is the original fixed
lifespan sum, after the exact multiplicities of ordered births cancel. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedGuardedSourceTraceBoundaryPairing_eq_fixedLifespans
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (q ρ θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i p, GiantTwoSidedPatternCoefficient PB (C i p) ell)
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    (hq : 0 < q) (hq1 : q < 1) (hn : 0 < n)
    (hV : ∀ g, bandReciprocalMass (PB g) ≠ 0) (hρ : ρ ≠ 0)
    (hb : ∀ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeBaseline (markedMemoryVisitQ q n) p.val ≠ 0) :
    let visitQ := markedMemoryVisitQ q n
    let ν (g : B) := giantSignedTiltedPrimeLaw (PB g) visitQ
    let V (g : B) := bandReciprocalMass (PB g)
    let rows := giantSignedChronologicalTraceRows (PS := PS) ν V q ρ θ n patterns C κ visitQ ζ K (fun _ _ _ _ => 1)
    giantSignedGuardedTraceBoundaryPairing (PS := PS) ν rows
      (giantSignedTraceBirthDistinctIndicator ν V q ρ θ n patterns C κ visitQ ζ K (fun _ _ _ _ => 1)) =
      ∑ p : (i : Fin n) → ↥(patterns i),
        ∑ path : GiantSignedLifespanOriginalPath PS PB (ell := ell) (fun i => C i (p i).val) κ,
          ∑ c : GiantSignedFixedLifespanChoices path visitQ,
            giantSignedFixedLifespanSourceWeight path q ζ (fun i => K i (p i).val) (θ : AddCircle (1 : ℝ)) c := by
  intro visitQ ν V rows
  have hvisit0 (i : Fin (n+1)) : 0 < visitQ i := by
    change 0 < markedMemoryVisitQ q n i
    unfold markedMemoryVisitQ
    split_ifs
    · exact Real.sqrt_pos.2 hq
    · exact hq
  have hvisit1 (i : Fin (n+1)) : visitQ i < 1 := by
    change markedMemoryVisitQ q n i < 1
    unfold markedMemoryVisitQ
    split_ifs
    · rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt hq.le hq1
    · exact hq1
  have hbase (g : B) (p : PB g) : giantSignedPrimeResidueBaseline p.val visitQ ≠ 0 := hb (giantTwoSidedResidueIndex g p)
  let Orders := GiantSignedSelectedOrderedLifespan PS PB ell patterns C κ visitQ
  let weight (p : (i : Fin n) → ↥(patterns i))
      (path : GiantSignedLifespanOriginalPath PS PB (ell := ell) (fun i => C i (p i).val) κ)
      (c : GiantSignedFixedLifespanChoices path visitQ) : ℂ :=
    giantSignedFixedLifespanSourceWeight path q ζ (fun i => K i (p i).val) (θ : AddCircle (1 : ℝ)) c
  calc
    _ = ∑ x : Orders, giantSignedChronologicalDistinctWeight ν V κ q visitQ ρ θ ζ
          (fun i => K i (x.1 i).val)
          (giantSignedFixedOrderedLifespan_chronology hP hdis hκ hsize x.2).2 :=
      giantSignedGuardedTraceBoundaryPairing_eq_orderedLifespan_sum ν V q ρ θ patterns C κ visitQ ζ K
        hP hdis hκ hsize hvisit0 hvisit1 hbase
    _ = ∑ x : Orders, giantSignedChronologicalBirthFactor
          (fun i g => (giantSignedGhostVisitBorn (x.2.2.1.val g) i).card) * weight x.1 x.2.1 x.2.2.1 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [giantSignedFixedOrderedLifespan_weight_eq q ρ θ ζ (fun i => K i (x.1 i).val)
        hP hdis hκ hsize hq.le hn hV hρ hb x.2]
      unfold weight giantSignedFixedLifespanSourceWeight
      change _ * giantSignedChronologicalBirthFactor
          (fun i g => (giantSignedGhostVisitBorn (x.2.2.1.val g) i).card) * _ = _
      ac_rfl
    _ = _ := giantSignedSelectedOrderedLifespan_sum_birth_factor patterns C κ visitQ weight

end
end ArtinMatthews
