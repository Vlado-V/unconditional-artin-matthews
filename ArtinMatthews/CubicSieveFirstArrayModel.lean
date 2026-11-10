module

public import ArtinMatthews.CubicSieveSelectedModel
public import ArtinMatthews.MarkedArrayEulerModel
public import ArtinMatthews.CubicSamplingArrayTruncation
public import ArtinMatthews.CubicSieveFirstArrayMass
public import ArtinMatthews.MarkedArrayMass
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! The first-array Euler models keep the actual represented tuple and
total-degree truncation before identifying the full Bernoulli expectation. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveFirstArrayFullModel {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (g : ℕ → ℝ) : ℝ :=
  ∑ t ∈ representedArrayChoices P (fun _ => 1),
    representedArrayCoefficient V (fun _ => 1) t *
      cubicSieveSelectedModel (univ.biUnion P) (representedArraySelected t)
        (representedArrayDamping univ P (fun _ => 1) (1 / 2)) g

def cubicSieveFirstArrayTruncationModel {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (g : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ representedArrayChoices P (fun _ => 1),
    representedArrayCoefficient V (fun _ => 1) t *
      cubicSieveSelectedTruncation (univ.biUnion P) (representedArraySelected t)
        (representedArrayDamping univ P (fun _ => 1) (1 / 2)) g k

def cubicSieveFirstArrayFullTangent {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (g v : ℕ → ℝ) : ℝ :=
  ∑ t ∈ representedArrayChoices P (fun _ => 1),
    representedArrayCoefficient V (fun _ => 1) t *
      cubicSieveSelectedModelTangent (univ.biUnion P) (representedArraySelected t)
        (representedArrayDamping univ P (fun _ => 1) (1 / 2)) g v

def cubicSieveFirstArrayTruncationTangent {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (g v : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ representedArrayChoices P (fun _ => 1),
    representedArrayCoefficient V (fun _ => 1) t *
      cubicSieveSelectedTruncationTangent (univ.biUnion P) (representedArraySelected t)
        (representedArrayDamping univ P (fun _ => 1) (1 / 2)) g v k

theorem cubicSieve_selectedModel_disjoint_union {J : Type*} [Fintype J]
    (P S : J → Finset ℕ) (θ g : ℕ → ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) (hS : ∀ j, S j ⊆ P j) :
    cubicSieveSelectedModel (univ.biUnion P) (univ.biUnion S) θ g =
      ∏ j, cubicSieveSelectedModel (P j) (S j) θ g := by
  have hP : ((Finset.univ : Finset J) : Set J).PairwiseDisjoint P := fun _ _ _ _ h => hdis h
  have hT : ((Finset.univ : Finset J) : Set J).PairwiseDisjoint S :=
    fun i _ j _ h => (hdis h).mono (hS i) (hS j)
  have hR : ((Finset.univ : Finset J) : Set J).PairwiseDisjoint (fun j => P j \ S j) :=
    fun _ _ _ _ h => (hdis h).mono sdiff_subset sdiff_subset
  unfold cubicSieveSelectedModel
  rw [disjoint_bands_residual_union univ P S hP (fun j _ => hS j),
    prod_biUnion hT, prod_biUnion hR, ← prod_mul_distrib]

theorem cubicSieve_firstArrayDamping_eq {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    {p : ℕ} (hp : p ∈ univ.biUnion P) :
    representedArrayDamping univ P (fun _ => 1) (1 / 2) p = 1 / 2 := by
  classical
  obtain ⟨j, hj, hp⟩ := mem_biUnion.mp hp
  rw [representedArrayDamping_on_band univ P (fun _ => 1) (1 / 2)
    (fun i _ k _ h => hdis h) hj hp]
  norm_num

private theorem cubicSieve_sum_finOne (P : Finset ℕ) (f : ℕ → ℝ) :
    (∑ t ∈ Fintype.piFinset (fun _ : Fin 1 => P), f (t 0)) = ∑ p ∈ P, f p := by
  classical
  apply sum_bij (fun t _ => t 0)
  · intro t ht
    exact Fintype.mem_piFinset.mp ht 0
  · intro t _ u _ h
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using h
  · intro p hp
    exact ⟨fun _ => p, Fintype.mem_piFinset.mpr (fun _ => hp), rfl⟩
  · intro _ _
    rfl

theorem cubicSieve_firstArrayFullModel_eq_bandMeans {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (g : ℕ → ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) :
    cubicSieveFirstArrayFullModel P V g = ∏ j, bernoulliBandMean (P j) g (V j) := by
  classical
  let F (j : J) (t : Fin 1 → ℕ) :=
    g (t 0) * ∏ p ∈ (P j).erase (t 0), (1 - (1 / 2 : ℝ) * g p)
  have hlocal (j : J) (t : Fin 1 → ℕ) :
      cubicSieveSelectedModel (P j) (representedChoiceSet t) (fun _ => 1 / 2) g = F j t := by
    simp only [cubicSieveSelectedModel, representedChoiceSet_one, prod_singleton, sdiff_singleton_eq_erase, F]
  have hsum (t : (j : J) → Fin 1 → ℕ) (ht : t ∈ representedArrayChoices P (fun _ => 1)) :
      cubicSieveSelectedModel (univ.biUnion P) (representedArraySelected t)
        (representedArrayDamping univ P (fun _ => 1) (1 / 2)) g = ∏ j, F j (t j) := by
    have hS (j : J) : representedChoiceSet (t j) ⊆ P j :=
      representedChoiceSet_subset (Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp ht j))
    have hhalf : cubicSieveSelectedModel (univ.biUnion P) (representedArraySelected t)
        (representedArrayDamping univ P (fun _ => 1) (1 / 2)) g =
      cubicSieveSelectedModel (univ.biUnion P) (representedArraySelected t) (fun _ => 1 / 2) g := by
      unfold cubicSieveSelectedModel
      congr 1
      apply prod_congr rfl
      intro p hp
      rw [cubicSieve_firstArrayDamping_eq P hdis (mem_sdiff.mp hp).1]
    rw [hhalf, representedArraySelected, cubicSieve_selectedModel_disjoint_union P _ _ _ hdis hS]
    exact prod_congr rfl (fun j _ => hlocal j (t j))
  calc
    _ = (∑ t ∈ representedArrayChoices P (fun _ => 1), ∏ j, F j (t j)) / ∏ j, V j := by
      unfold cubicSieveFirstArrayFullModel
      rw [sum_div]
      apply sum_congr rfl
      intro t ht
      rw [cubicSieve_firstArray_coefficient V t, hsum t ht]
      ring
    _ = (∏ j, ∑ t ∈ Fintype.piFinset (fun _ : Fin 1 => P j), F j t) / ∏ j, V j := by
      rw [prod_univ_sum]
      rfl
    _ = _ := by
      rw [← prod_div_distrib]
      apply prod_congr rfl
      intro j _
      rw [bernoulliBandMean_eq]
      dsimp only [F]
      rw [cubicSieve_sum_finOne (P j) (fun p => g p * ∏ q ∈ (P j).erase p, (1 - (1 / 2 : ℝ) * g q))]
      congr 1
      apply sum_congr rfl
      intro p _
      congr 1
      apply prod_congr rfl
      intro q _
      ring

theorem cubicSieve_firstArrayFullModel_hasDerivAt {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (G : ℕ → ℝ → ℝ) (v : ℕ → ℝ) (s : ℝ)
    (hv : ∀ p ∈ univ.biUnion P, HasDerivAt (G p) (v p) s) :
    HasDerivAt (fun t => cubicSieveFirstArrayFullModel P V (fun p => G p t))
      (cubicSieveFirstArrayFullTangent P V (fun p => G p s) v) s := by
  unfold cubicSieveFirstArrayFullModel cubicSieveFirstArrayFullTangent
  apply HasDerivAt.fun_sum
  intro t ht
  exact (cubicSieve_selectedModel_hasDerivAt _ _ (cubicSampling_selected_subset P (fun _ => 1) ht)
    _ G v s hv).const_mul _

theorem cubicSieve_firstArrayTruncationModel_hasDerivAt {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (G : ℕ → ℝ → ℝ) (v : ℕ → ℝ) (s : ℝ)
    (hv : ∀ p ∈ univ.biUnion P, HasDerivAt (G p) (v p) s) (k : ℕ) :
    HasDerivAt (fun t => cubicSieveFirstArrayTruncationModel P V (fun p => G p t) k)
      (cubicSieveFirstArrayTruncationTangent P V (fun p => G p s) v k) s := by
  unfold cubicSieveFirstArrayTruncationModel cubicSieveFirstArrayTruncationTangent
  apply HasDerivAt.fun_sum
  intro t ht
  exact (cubicSieve_selectedTruncation_hasDerivAt _ _ (cubicSampling_selected_subset P (fun _ => 1) ht)
    _ G v s hv k).const_mul _

end ArtinMatthews
