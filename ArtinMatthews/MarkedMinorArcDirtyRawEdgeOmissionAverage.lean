module

public import ArtinMatthews.MarkedMinorArcRawSlotAverage
public import ArtinMatthews.MarkedMinorArcRawGoodFirst
public import ArtinMatthews.MarkedMinorArcDirtyPermutation
public import ArtinMatthews.MarkedMinorArcDirtyPermutationAction
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source slot symmetrization is exactly the uniform omission
expectation for every finite test, including all internal slot orders. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtySourceSlotWeight {J : Type*} [Fintype J] (n : ℕ)
    (_σ : J → Equiv.Perm (Fin (n+1))) : ℝ :=
  ∏ _j : J, 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ)

theorem markedDirtySourceSlotWeight_eq {J : Type*} [Fintype J] [DecidableEq J] (n : ℕ)
    (σ : J → Equiv.Perm (Fin (n+1))) :
    markedDirtySourceSlotWeight n σ = 1/(Fintype.card (J → Equiv.Perm (Fin (n+1))):ℝ) := by
  simp [markedDirtySourceSlotWeight,one_div]

theorem markedDirtySourceOmission_fiber_mass {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (slot : Fin (n+1)) (o : J → Fin (n+1)) :
    (∑ σ : J → Equiv.Perm (Fin (n+1)),
      if (fun j => σ j slot)=o then markedDirtySourceSlotWeight n σ else 0)=
        markedUniformOmissionWeight (n+1) o := by
  classical
  have he (σ : J → Equiv.Perm (Fin (n+1))) :
      (if (fun j => σ j slot)=o then markedDirtySourceSlotWeight n σ else 0)=
        ∏ j, if σ j slot=o j then 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0 := by
    by_cases hall : ∀ j, σ j slot=o j
    · rw [ite_eq_left (funext hall)]
      unfold markedDirtySourceSlotWeight
      exact Finset.prod_congr rfl (fun j _ => (ite_eq_left (hall j)).symm)
    · rw [ite_eq_right (fun h => hall (congrFun h))]
      obtain ⟨j,hj⟩ := not_forall.mp hall
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)).symm
  simp_rw [he]
  rw [← Fintype.prod_sum (fun j (σ : Equiv.Perm (Fin (n+1))) =>
    if σ slot=o j then 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0)]
  simp_rw [markedPermutation_slot_probability]
  simp only [markedUniformOmissionWeight,Nat.cast_add,Nat.cast_one]

theorem markedDirtySourceOmission_expectation {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (slot : Fin (n+1)) (f : (J → Fin (n+1)) → ℝ) :
    (∑ σ : J → Equiv.Perm (Fin (n+1)), markedDirtySourceSlotWeight n σ*f (fun j => σ j slot))=
      ∑ o : J → Fin (n+1), markedUniformOmissionWeight (n+1) o*f o := by
  classical
  have he (σ : J → Equiv.Perm (Fin (n+1))) :
      markedDirtySourceSlotWeight n σ*f (fun j => σ j slot)=
        ∑ o : J → Fin (n+1),
          (if (fun j => σ j slot)=o then markedDirtySourceSlotWeight n σ else 0)*f o := by
    rw [Fintype.sum_eq_single (fun j => σ j slot)]
    · simp
    · intro o ho
      simp only [ite_eq_right ho.symm,zero_mul]
  calc
    _ = ∑ σ : J → Equiv.Perm (Fin (n+1)), ∑ o : J → Fin (n+1),
        (if (fun j => σ j slot)=o then markedDirtySourceSlotWeight n σ else 0)*f o :=
      Finset.sum_congr rfl (fun σ _ => he σ)
    _ = ∑ o : J → Fin (n+1), (∑ σ : J → Equiv.Perm (Fin (n+1)),
        if (fun j => σ j slot)=o then markedDirtySourceSlotWeight n σ else 0)*f o := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun _ _ => (Finset.sum_mul _ _ _).symm)
    _ = _ := by simp_rw [markedDirtySourceOmission_fiber_mass]

/-- This is the literal copied-prefix product under the actual state slot
permutation, before any physical or analytic test is imposed. -/
theorem markedDirtyRawStateSlot_copied_product {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin (pads+1))) (s : MarkedRawState P (pads+1) B Z) :
    markedRawCopiedProduct ((markedRawActiveSplit pads) (markedRawSlotEquiv σ s).2.1).1=
      markedSourceCopiedProduct (markedRawNumericActive s.2.1) (fun j => σ j (Fin.last pads)) := by
  rw [markedRawCopiedProduct_eq_source]
  exact markedSourceCopiedProduct_permuted (markedRawNumericActive s.2.1) σ (fun _ => Fin.last pads)

end ArtinMatthews
