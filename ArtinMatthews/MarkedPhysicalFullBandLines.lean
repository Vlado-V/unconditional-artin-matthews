module

public import ArtinMatthews.MarkedPhysicalBonferroniMarginal
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

/-! A single full-band line tuple carries every performed monomial.
The common integrand preserves active flags and all visits at one prime;
the selected modulus is used only for the exact finite marginal. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev MarkedPhysicalBandLines {J : Type*} [Fintype J] (P : J → Finset ℕ) :=
  MarkedMemoryIndependentLines (markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j)))

def markedPhysicalBandPrimeIndex {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (p : ℕ) (hp : p ∈ markedPhysicalBandPrimes P) :
    ↥(markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j))) :=
  ⟨⟨p,markedPhysicalBandPrimes_prime hP hp⟩,by
    obtain ⟨j,hj,hjp⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_biUnion.mpr ⟨j,hj,(mem_markedRawPrimeBand _ _).mpr hjp⟩⟩

def markedPhysicalBandLineHit {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (p : ℕ) : Prop :=
  if hp : p ∈ markedPhysicalBandPrimes P then
    let _ : Fact p.Prime := ⟨markedPhysicalBandPrimes_prime hP hp⟩
    markedPrimePositionLine p z hz = ell (markedPhysicalBandPrimeIndex hP p hp)
  else False

def markedPhysicalBandLineVisitFactor {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (active : Finset ℕ) (r : ℝ) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (p : ℕ) : ℝ :=
  if p ∈ active then 1 else if markedPhysicalBandLineHit hP ell z hz p then r else 1

def markedPhysicalBandLinePrimePathFactor {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (p : ℕ) : ℝ :=
  ∏ v ∈ I,markedPhysicalBandLineVisitFactor hP ell (markedPhysicalActivePrimes (a v)) (r v) (z v) (hz v) p

def markedPhysicalBandLineMonomial {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ) : ℝ :=
  (∏ p ∈ markedPhysicalPathUsedPrimes I a,markedPhysicalBandLinePrimePathFactor hP ell I a r z hz p)*
    ∏ p ∈ T,(1-markedPhysicalBandLinePrimePathFactor hP ell I a r z hz p)

def markedPhysicalBandLineTail {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ) : ℝ :=
  ∑ T ∈ (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a).powersetCard k,
    markedPhysicalBandLineMonomial hP ell I a r z hz T

theorem markedPhysicalSelectedLines_hit_iff
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    {T : Finset ℕ} (hT : T ⊆ markedPhysicalBandPrimes P) (ell : MarkedPhysicalBandLines P)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) {p : ℕ}
    (hp : p ∈ (markedPhysicalBonferroniModulus I a T).primeFactors) :
    markedPhysicalLineTupleHit
        (markedPhysicalFullLinesRootRestrict (markedPhysicalBonferroniModulus_full_band_subset hP I a hT) ell) z hz p ↔
      markedPhysicalBandLineHit hP ell z hz p := by
  have hband : p ∈ markedPhysicalBandPrimes P := by
    rw [markedPhysicalBonferroniModulus_primeFactors_eq hP I a hT] at hp
    rcases Finset.mem_union.mp hp with hu | ht
    · exact markedPhysicalPathUsedPrimes_subset I a hu
    · exact hT ht
  simp only [markedPhysicalLineTupleHit,dite_eq_left hp,
    markedPhysicalBandLineHit,dite_eq_left hband,markedPhysicalFullLinesRootRestrict_apply]
  rfl

theorem markedPhysicalSelectedLines_prime_factor
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (r : ι → ℝ) (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)
    {T : Finset ℕ} (hT : T ⊆ markedPhysicalBandPrimes P) (ell : MarkedPhysicalBandLines P) {p : ℕ}
    (hp : p ∈ (markedPhysicalBonferroniModulus I a T).primeFactors) :
    markedPhysicalLinePrimePathFactor
        (markedPhysicalFullLinesRootRestrict (markedPhysicalBonferroniModulus_full_band_subset hP I a hT) ell) I a r z hz p =
      markedPhysicalBandLinePrimePathFactor hP ell I a r z hz p := by
  apply Finset.prod_congr rfl
  intro v _
  simp only [markedPhysicalLineVisitFactor,markedPhysicalBandLineVisitFactor,
    markedPhysicalSelectedLines_hit_iff hP I a hT ell (z v) (hz v) hp]

theorem markedPhysicalSelectedLines_monomial
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (r : ι → ℝ) (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)
    {T : Finset ℕ} (hT : T ⊆ markedPhysicalBandPrimes P) (ell : MarkedPhysicalBandLines P) :
    markedPhysicalLineBonferroniMonomial
        (markedPhysicalFullLinesRootRestrict (markedPhysicalBonferroniModulus_full_band_subset hP I a hT) ell) I a r z hz T =
      markedPhysicalBandLineMonomial hP ell I a r z hz T := by
  unfold markedPhysicalLineBonferroniMonomial markedPhysicalBandLineMonomial
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    exact markedPhysicalSelectedLines_prime_factor hP I a r z hz hT ell
      (markedPhysicalBonferroniModulus_mem_primeFactors hP I a hT (Finset.mem_union_left T hp))
  · apply Finset.prod_congr rfl
    intro p hp
    unfold markedPhysicalLinePrimeLoss
    rw [markedPhysicalSelectedLines_prime_factor hP I a r z hz hT ell
      (markedPhysicalBonferroniModulus_mem_primeFactors hP I a hT (Finset.mem_union_right _ hp))]

theorem markedPhysicalSelectedMonomialMean_common_lines
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (r : ι → ℝ) (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)
    {T : Finset ℕ} (hT : T ⊆ markedPhysicalBandPrimes P) :
    markedPhysicalSelectedMonomialMean hP I a r z hz T =
      (∑ ell : MarkedPhysicalBandLines P,markedPhysicalBandLineMonomial hP ell I a r z hz T)/
        (Fintype.card (MarkedPhysicalBandLines P):ℝ) := by
  rw [markedPhysicalSelectedMonomialMean_full_lines hP I a r z hz T hT]
  congr 1
  apply Finset.sum_congr rfl
  intro ell _
  exact markedPhysicalSelectedLines_monomial hP I a r z hz hT ell

theorem markedPhysicalBonferroniTailMean_common_lines
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (r : ι → ℝ) (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ) :
    markedPhysicalBonferroniTailMean hP I a r z hz k =
      (∑ ell : MarkedPhysicalBandLines P,markedPhysicalBandLineTail hP ell I a r z hz k)/
        (Fintype.card (MarkedPhysicalBandLines P):ℝ) := by
  calc
    _ = ∑ T ∈ (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes I a).powersetCard k,
        (∑ ell : MarkedPhysicalBandLines P,markedPhysicalBandLineMonomial hP ell I a r z hz T)/
          (Fintype.card (MarkedPhysicalBandLines P):ℝ) := by
      apply Finset.sum_congr rfl
      intro T hT
      exact markedPhysicalSelectedMonomialMean_common_lines hP I a r z hz
        (fun p hp => (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hT).1 hp)).1)
    _ = _ := by
      rw [← Finset.sum_div,Finset.sum_comm]
      rfl

end ArtinMatthews
