module

public import ArtinMatthews.MarkedFiniteLineMarginal
public import ArtinMatthews.MarkedPhysicalBonferroniTailMean
public import ArtinMatthews.MarkedMemoryBandPrimeEquiv
public import ArtinMatthews.MarkedPhysicalBonferroniCRT
public import ArtinMatthews.MarkedPhysicalBonferroniMonomialMean
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

/-! The performed selected-modulus mean is exactly a marginal of the
actual full-band independent-line tuple. This is finite reindexing, and
retains arbitrary selected-prime observables and repeated-visit coupling. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalRootLinesPrimeEquiv (S : ℕ) :
    MarkedRootLineTuple S ≃ MarkedMemoryIndependentLines (markedRawPrimeBand S.primeFactors) where
  toFun ell p := ell ⟨(p.1:ℕ),(mem_markedRawPrimeBand S.primeFactors p.1).mp p.2⟩
  invFun ell p := ell ⟨⟨p.1,(Nat.mem_primeFactors.mp p.2).1⟩,
    (mem_markedRawPrimeBand S.primeFactors _).mpr p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def markedPhysicalFullLinesRootRestrict {S : ℕ} {U : Finset Nat.Primes}
    (hU : markedRawPrimeBand S.primeFactors ⊆ U)
    (ell : MarkedMemoryIndependentLines U) : MarkedRootLineTuple S :=
  (markedPhysicalRootLinesPrimeEquiv S).symm (markedFiniteSubsetPiRestrict hU MarkedRawPrimeLine ell)

theorem markedPhysicalFullLinesRootRestrict_apply {S : ℕ} {U : Finset Nat.Primes}
    (hU : markedRawPrimeBand S.primeFactors ⊆ U)
    (ell : MarkedMemoryIndependentLines U) (p : S.primeFactors) :
    markedPhysicalFullLinesRootRestrict hU ell p =
      ell ⟨⟨p.1,(Nat.mem_primeFactors.mp p.2).1⟩,
        hU ((mem_markedRawPrimeBand S.primeFactors _).mpr p.2)⟩ := rfl

theorem marked_squarefree_root_average_full_lines {S : ℕ} [NeZero S]
    (hS : Squarefree S) (U : Finset Nat.Primes)
    (hU : markedRawPrimeBand S.primeFactors ⊆ U) (f : MarkedRootLineTuple S → ℝ) :
    (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),f (markedRootKernelTuple hS g))/
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ) =
      (∑ ell : MarkedMemoryIndependentLines U,f (markedPhysicalFullLinesRootRestrict hU ell))/
        (Fintype.card (MarkedMemoryIndependentLines U):ℝ) := by
  rw [marked_squarefree_root_kernel_tuple_average_real,← markedPhysicalLineTuple_card S]
  let e := markedPhysicalRootLinesPrimeEquiv S
  have he : (∑ ell : MarkedRootLineTuple S,f ell)/(Fintype.card (MarkedRootLineTuple S):ℝ) =
      (∑ ell : MarkedMemoryIndependentLines (markedRawPrimeBand S.primeFactors),f (e.symm ell))/
        (Fintype.card (MarkedMemoryIndependentLines (markedRawPrimeBand S.primeFactors)):ℝ) := by
    rw [← Fintype.card_congr e]
    congr 1
    exact (Equiv.sum_comp e.symm f).symm
  exact he.trans (markedMemoryIndependentLines_marginal _ U hU (fun ell => f (e.symm ell))).symm

theorem markedPhysicalBonferroniModulus_primeFactors_eq
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) {M : ℕ}
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) {T : Finset ℕ}
    (hT : T ⊆ markedPhysicalBandPrimes P) :
    (markedPhysicalBonferroniModulus I a T).primeFactors = markedPhysicalPathUsedPrimes I a ∪ T :=
  Nat.primeFactors_prod (fun _ hp => markedPhysicalBonferroniModulus_prime hP I a hT hp)

theorem markedPhysicalBonferroniModulus_full_band_subset
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) {M : ℕ}
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) {T : Finset ℕ}
    (hT : T ⊆ markedPhysicalBandPrimes P) :
    markedRawPrimeBand (markedPhysicalBonferroniModulus I a T).primeFactors ⊆
      markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j)) := by
  intro p hp
  have hp' := (mem_markedRawPrimeBand _ p).mp hp
  rw [markedPhysicalBonferroniModulus_primeFactors_eq hP I a hT] at hp'
  have hband : (p:ℕ) ∈ markedPhysicalBandPrimes P := by
    rcases Finset.mem_union.mp hp' with hused | hsel
    · exact markedPhysicalPathUsedPrimes_subset I a hused
    · exact hT hsel
  obtain ⟨j,hj,hp⟩ := Finset.mem_biUnion.mp hband
  exact Finset.mem_biUnion.mpr ⟨j,hj,(mem_markedRawPrimeBand (P j) p).mpr hp⟩

theorem markedPhysicalSelectedMonomialMean_full_lines
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) {M : ℕ}
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ)
    (hT : T ⊆ markedPhysicalBandPrimes P) :
    markedPhysicalSelectedMonomialMean hP I a r z hz T =
      (∑ ell : MarkedMemoryIndependentLines (markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j))),
        markedPhysicalLineBonferroniMonomial
          (markedPhysicalFullLinesRootRestrict (markedPhysicalBonferroniModulus_full_band_subset hP I a hT) ell)
          I a r z hz T)/
        (Fintype.card (MarkedMemoryIndependentLines (markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j)))):ℝ) := by
  let S := markedPhysicalBonferroniModulus I a T
  let : NeZero S := ⟨(markedPhysicalBonferroniModulus_pos hP I a hT).ne'⟩
  simp only [markedPhysicalSelectedMonomialMean,dite_eq_left hT]
  exact marked_squarefree_root_average_full_lines _ _ _
    (fun ell => markedPhysicalLineBonferroniMonomial ell I a r z hz T)

end ArtinMatthews
