module

public import ArtinMatthews.MarkedPhysicalBandLineIndex
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The exact full-band independent-line observable is the actual
active-line incidence guard times the common inactive damping product.
All factors use the literal physical labels and the original VisitQ. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalBandLineWeight {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) : ℝ :=
  ∏ p ∈ markedPhysicalBandPrimes P,markedPhysicalBandLinePrimePathFactor hP ell I a r z hz p

def MarkedPhysicalBandLineGuard {J : Type*} [Fintype J] {P : J → Finset ℕ} {M N : ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (a : Fin (N+1) → MarkedPhysicalMarking P M)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)
    (ell : MarkedPhysicalBandLines P) : Prop :=
  ∀ p : ↥(markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j))),
    ∀ v ∈ markedMemoryActiveVisits (markedPhysicalMarkingPathRawSlots hP a) p.1,
      markedMemoryPositionLines p.1 z hz v = ell p

theorem markedPhysicalBandLineWeight_typed {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (ell : MarkedPhysicalBandLines P) (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (r : ι → ℝ) (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) :
    markedPhysicalBandLineWeight hP ell I a r z hz =
      ∏ p : ↥(markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j))),
        markedPhysicalBandLinePrimePathFactor hP ell I a r z hz (p.1:ℕ) := by
  rw [markedPhysicalBandLineWeight,← Finset.prod_coe_sort]
  exact Equiv.prod_comp (markedPhysicalBandPrimeIndexEquiv hP)
    (fun p => markedPhysicalBandLinePrimePathFactor hP ell I a r z hz (p.1:ℕ))

theorem markedPhysicalPathLineFactor_eq {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M N : ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (a : Fin (N+1) → MarkedPhysicalMarking P M) (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)
    (ell : MarkedPhysicalBandLines P)
    (p : ↥(markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j)))) :
    markedMemoryPathLineFactor _ (markedPhysicalMarkingPathRawSlots hP a) q z hz p (ell p) =
      (if ∀ v ∈ markedMemoryActiveVisits (markedPhysicalMarkingPathRawSlots hP a) p.1,
          markedMemoryPositionLines p.1 z hz v = ell p then 1 else 0)*
        markedPhysicalBandLinePrimePathFactor hP ell Finset.univ a (markedMemoryVisitQ q N) z hz (p.1:ℕ) := by
  rw [markedMemoryPathLineFactor,markedPhysicalBandLinePrimePathFactor_inactive]
  congr 1
  by_cases h : ∀ v ∈ markedMemoryActiveVisits (markedPhysicalMarkingPathRawSlots hP a) p.1,
      markedMemoryPositionLines p.1 z hz v = ell p
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro v hv
    simp [markedLineHit,h v hv]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨v,hv,hvne⟩ := h
    exact Finset.prod_eq_zero hv (by simp [markedLineHit,Ne.symm hvne])

theorem markedPhysicalBandLineObservable_eq {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M N : ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (a : Fin (N+1) → MarkedPhysicalMarking P M) (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)
    (ell : MarkedPhysicalBandLines P) :
    (∏ p : ↥(markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j))),
      markedMemoryPathLineFactor _ (markedPhysicalMarkingPathRawSlots hP a) q z hz p (ell p)) =
      if MarkedPhysicalBandLineGuard hP a z hz ell then
        markedPhysicalBandLineWeight hP ell Finset.univ a (markedMemoryVisitQ q N) z hz else 0 := by
  by_cases h : MarkedPhysicalBandLineGuard hP a z hz ell
  · rw [ite_eq_left h,markedPhysicalBandLineWeight_typed]
    apply Finset.prod_congr rfl
    intro p _
    rw [markedPhysicalPathLineFactor_eq hP a q z hz ell p,ite_eq_left (h p),one_mul]
  · rw [ite_eq_right h]
    have hh : ¬(∀ p : ↥(markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j))),
        ∀ v ∈ markedMemoryActiveVisits (markedPhysicalMarkingPathRawSlots hP a) p.1,
          markedMemoryPositionLines p.1 z hz v = ell p) := h
    obtain ⟨p,hp⟩ := not_forall.mp hh
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    rw [markedPhysicalPathLineFactor_eq hP a q z hz ell p,ite_eq_right hp,zero_mul]

theorem markedPhysicalIndependentLineExpectation_eq {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M N : ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (a : Fin (N+1) → MarkedPhysicalMarking P M) (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) :
    markedMemoryIndependentLineExpectation (markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j)))
      (markedPhysicalMarkingPathRawSlots hP a) q z hz =
      (∑ ell : MarkedPhysicalBandLines P,
        if MarkedPhysicalBandLineGuard hP a z hz ell then
          markedPhysicalBandLineWeight hP ell Finset.univ a (markedMemoryVisitQ q N) z hz else 0)/
        (Fintype.card (MarkedPhysicalBandLines P):ℝ) := by
  unfold markedMemoryIndependentLineExpectation
  congr 1
  apply Finset.sum_congr rfl
  intro ell _
  exact markedPhysicalBandLineObservable_eq hP a q z hz ell

end ArtinMatthews
