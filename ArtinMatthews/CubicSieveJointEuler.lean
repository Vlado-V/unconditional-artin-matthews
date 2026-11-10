module

public import ArtinMatthews.CubicSieveProgressionEuler
public import ArtinMatthews.CubicSieveFirstArrayModel
public import ArtinMatthews.CubicSieveRestrictedDensity
public import ArtinMatthews.CubicSamplingArrayTruncation
public import ArtinMatthews.CubicSieveFirstArrayTail
public import ArtinMatthews.CubicSieveMarkingProduct
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

/-! The actual retained-array Euler sum and the original correction
polynomial combine into the finite factor J_h of (7.12). -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveFirstArrayEulerSum {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (k r : ℕ) (s : ℝ) : ℝ :=
  ∑ t ∈ representedArrayChoices P (fun _ => 1),
    ∑ i ∈ markedWeightedIndices (univ.biUnion P) (representedArraySelected t) k,
      (representedArrayCoefficient V (fun _ => 1) t *
        markedWeightedCoefficient (representedArrayDamping univ P (fun _ => 1) (1 / 2)) i) *
      (if (markedWeightedDivisor (representedArraySelected t) i).Coprime r then
        cubicSieveMarkingFactor (markedWeightedDivisor (representedArraySelected t) i) s else 0)

theorem cubicSieve_firstArrayEulerSum_eq_model {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (k r : ℕ) (s : ℝ) :
    cubicSieveFirstArrayEulerSum P V k r s =
      cubicSieveFirstArrayTruncationModel P V (fun p => cubicSieveRestrictedMarkingDensity r p s) k := by
  rw [cubicSieve_firstArrayTruncation_coefficients]
  unfold cubicSieveFirstArrayEulerSum
  apply sum_congr rfl
  intro t ht
  apply sum_congr rfl
  intro i hi
  rw [cubicSieve_markedWeightedDivisor_restricted_product _ _
    (fun p hp => by
      obtain ⟨j, _, hp⟩ := mem_biUnion.mp hp
      exact hP j p hp)
    (cubicSampling_selected_subset P (fun _ => 1) ht) hi r s]

theorem cubicSieve_firstArrayEulerSum_hasDerivAt_one {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (hP : ∀ j p, p ∈ P j → p.Prime) (k r : ℕ) :
    HasDerivAt (cubicSieveFirstArrayEulerSum P V k r)
      (cubicSieveFirstArrayTruncationTangent P V (fun p => cubicSieveRestrictedMarkingDensity r p 1)
        (cubicSieveRestrictedMarkingTangent r) k) 1 := by
  have heq : cubicSieveFirstArrayEulerSum P V k r =
      fun s => cubicSieveFirstArrayTruncationModel P V (fun p => cubicSieveRestrictedMarkingDensity r p s) k :=
    funext (fun s => cubicSieve_firstArrayEulerSum_eq_model P V hP k r s)
  rw [heq]
  exact cubicSieve_firstArrayTruncationModel_hasDerivAt P V
    (fun p s => cubicSieveRestrictedMarkingDensity r p s) _ 1
    (fun p hp => by
      obtain ⟨j, _, hp⟩ := mem_biUnion.mp hp
      exact cubicSieve_restrictedMarkingDensity_hasDerivAt_one r (hP j p hp).one_lt) k

def cubicSieveJointEulerModel {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (z : ℝ) (m k : ℕ) (s : ℝ) : ℝ :=
  ∑ R ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m R *
    (cubicSieveDivisorFactor (roughSubsetDivisor R) s *
      cubicSieveFirstArrayEulerSum P V k (roughSubsetDivisor R) s)

def cubicSieveJointEulerTangent {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (z : ℝ) (m k : ℕ) : ℝ :=
  ∑ R ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m R *
    ((-cubicSieveDivisorLogMoment (roughSubsetDivisor R)) *
      cubicSieveFirstArrayEulerSum P V k (roughSubsetDivisor R) 1 +
      cubicSieveDivisorLeading (roughSubsetDivisor R) *
        cubicSieveFirstArrayTruncationTangent P V
          (fun p => cubicSieveRestrictedMarkingDensity (roughSubsetDivisor R) p 1)
          (cubicSieveRestrictedMarkingTangent (roughSubsetDivisor R)) k)

theorem cubicSieve_jointEulerModel_hasDerivAt_one {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (z : ℝ) (m k : ℕ) :
    HasDerivAt (cubicSieveJointEulerModel P V z m k) (cubicSieveJointEulerTangent P V z m k) 1 := by
  unfold cubicSieveJointEulerModel cubicSieveJointEulerTangent
  apply HasDerivAt.fun_sum
  intro R hR
  have hr := roughSubsetDivisor_pos R (fun p hp => Nat.prime_of_mem_primesLE (mem_powerset.mp hR hp))
  have h := ((cubicSieve_divisorFactor_hasDerivAt_one hr).mul
    (cubicSieve_firstArrayEulerSum_hasDerivAt_one P V hP k (roughSubsetDivisor R))).const_mul
      (cubicSieveCorrectionCoeff z m R)
  convert! h using 1
  all_goals simp only [cubicSieve_divisorFactor_one hr]

end ArtinMatthews
