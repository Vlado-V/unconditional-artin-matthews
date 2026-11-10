module

public import ArtinMatthews.MarkedPhysicalBandLineObservable
public import ArtinMatthews.MarkedPhysicalPathResidueValidity
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

/-! The actual physical residue-validity test passes through the same
full-band marginal. Ordered-list distinctness remains an explicit
constant guard, and active incidences are the literal line guard. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalLineLabelValid {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M S : ℕ} (ell : MarkedRootLineTuple S)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) : Prop :=
  ∀ v∈I,MarkedPhysicalMarkingDistinct (a v) ∧
    ∀ j k,markedPhysicalLineTupleHit ell (z v) (hz v) (a v j k:ℕ)

theorem markedPhysicalBandLineGuard_iff_labels {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M N : ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (a : Fin (N+1) → MarkedPhysicalMarking P M)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)
    (ell : MarkedPhysicalBandLines P) :
    MarkedPhysicalBandLineGuard hP a z hz ell ↔
      ∀ v j k,markedPhysicalBandLineHit hP ell (z v) (hz v) (a v j k:ℕ) := by
  constructor
  · intro hg v j k
    have hactive : (a v j k:ℕ)∈markedPhysicalActivePrimes (a v) :=
      Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩
    have hband := markedPhysicalActivePrimes_subset (a v) hactive
    let p := markedPhysicalBandPrimeIndex hP (a v j k:ℕ) hband
    have hv : v∈markedMemoryActiveVisits (markedPhysicalMarkingPathRawSlots hP a) p.1 :=
      (markedPhysicalMarkingPath_active_iff hP a p.1 v).mp hactive
    exact (markedPhysicalBandLineHit_iff hP ell p (z v) (hz v)).mpr (hg p v hv)
  · intro h p v hv
    have ha := (markedPhysicalMarkingPath_active_iff hP a p.1 v).mpr hv
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hj
    have hh := h v j k
    rw [hk] at hh
    exact (markedPhysicalBandLineHit_iff hP ell p (z v) (hz v)).mp hh

theorem markedPhysicalSelectedLineLabelValid_iff {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M N : ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (a : Fin (N+1) → MarkedPhysicalMarking P M)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)
    {T : Finset ℕ} (hT : T⊆markedPhysicalBandPrimes P) (ell : MarkedPhysicalBandLines P) :
    markedPhysicalLineLabelValid
        (markedPhysicalFullLinesRootRestrict (markedPhysicalBonferroniModulus_full_band_subset hP Finset.univ a hT) ell)
        Finset.univ a z hz ↔
      (∀ v,MarkedPhysicalMarkingDistinct (a v)) ∧ MarkedPhysicalBandLineGuard hP a z hz ell := by
  have hh (v j k) := markedPhysicalSelectedLines_hit_iff hP Finset.univ a hT ell (z v) (hz v)
    (markedPhysicalBonferroniModulus_mem_primeFactors hP Finset.univ a hT
      (Finset.mem_union_left T (markedPhysical_label_mem_pathUsed Finset.univ a v (Finset.mem_univ v) j k)))
  constructor
  · intro h
    refine ⟨fun v => (h v (Finset.mem_univ v)).1,
      (markedPhysicalBandLineGuard_iff_labels hP a z hz ell).mpr ?_⟩
    intro v j k
    exact (hh v j k).mp ((h v (Finset.mem_univ v)).2 j k)
  · rintro ⟨hd,hg⟩ v _
    exact ⟨hd v,fun j k => (hh v j k).mpr
      ((markedPhysicalBandLineGuard_iff_labels hP a z hz ell).mp hg v j k)⟩

def markedPhysicalSelectedGuardedMonomialMean {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M N : ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (a : Fin (N+1) → MarkedPhysicalMarking P M) (r : Fin (N+1) → ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)
    (T : Finset ℕ) (hT : T⊆markedPhysicalBandPrimes P) : ℝ :=
  let S := markedPhysicalBonferroniModulus Finset.univ a T
  let _ : NeZero S := ⟨(markedPhysicalBonferroniModulus_pos hP Finset.univ a hT).ne'⟩
  (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
    if markedPhysicalResidueLabelValid (markedPhysicalBonferroniModulus_squarefree hP Finset.univ a hT) g Finset.univ a z hz
    then markedPhysicalResidueBonferroniMonomial (markedPhysicalBonferroniModulus_squarefree hP Finset.univ a hT)
      g Finset.univ a r z hz T else 0)/
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ)

theorem markedPhysicalSelectedGuardedMonomialMean_common_lines {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M N : ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (a : Fin (N+1) → MarkedPhysicalMarking P M) (r : Fin (N+1) → ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)
    (T : Finset ℕ) (hT : T⊆markedPhysicalBandPrimes P) :
    markedPhysicalSelectedGuardedMonomialMean hP a r z hz T hT =
      (∑ ell : MarkedPhysicalBandLines P,
        if (∀ v,MarkedPhysicalMarkingDistinct (a v)) ∧ MarkedPhysicalBandLineGuard hP a z hz ell then
          markedPhysicalBandLineMonomial hP ell Finset.univ a r z hz T else 0)/
        (Fintype.card (MarkedPhysicalBandLines P):ℝ) := by
  let S := markedPhysicalBonferroniModulus Finset.univ a T
  let : NeZero S := ⟨(markedPhysicalBonferroniModulus_pos hP Finset.univ a hT).ne'⟩
  have havg := marked_squarefree_root_average_full_lines
    (markedPhysicalBonferroniModulus_squarefree hP Finset.univ a hT) _
    (markedPhysicalBonferroniModulus_full_band_subset hP Finset.univ a hT)
    (fun ell => if markedPhysicalLineLabelValid ell Finset.univ a z hz then
      markedPhysicalLineBonferroniMonomial ell Finset.univ a r z hz T else 0)
  calc
    _ = _ := havg
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro ell _
      rw [markedPhysicalSelectedLineLabelValid_iff hP a z hz hT ell,
        markedPhysicalSelectedLines_monomial hP Finset.univ a r z hz hT ell]
      split_ifs <;> rfl

end ArtinMatthews
