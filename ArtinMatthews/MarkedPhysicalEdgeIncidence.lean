module

public import ArtinMatthews.MarkedPhysicalEdgeLabelSplit
public import ArtinMatthews.MarkedPhysicalRootResidue
public import ArtinMatthews.MarkedPhysicalEndpointArithmetic
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

/-! Actual source and target prime-line constraints over the distinct union
marking. Every prime of its modulus is constrained by at least one endpoint. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators LinearAlgebra.Projectivization
attribute [local instance] Classical.propDecidable

theorem markedPhysicalEdgeTarget_last {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (u : MarkedPhysicalMarking P (M+2)) (j : J) :
    markedPhysicalEdgeTarget u j (Fin.last M)=u j (Fin.last (M+1)) := by
  simp [markedPhysicalEdgeTarget,markedPhysicalMarkingSplit]

theorem markedPhysicalEdgeTarget_castSucc {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (u : MarkedPhysicalMarking P (M+2)) (j : J) (k : Fin M) :
    markedPhysicalEdgeTarget u j k.castSucc=u j k.castSucc.castSucc := by
  simp [markedPhysicalEdgeTarget,markedPhysicalEdgeSource,markedPhysicalMarkingSplit]

theorem markedPhysicalEdge_prime_coverage {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p ∈ P j → p.Prime) {M : ℕ}
    (u : MarkedPhysicalMarking P (M+2)) (p : (markedPhysicalMarkingProduct u).primeFactors) :
    (p : ℕ) ∣ markedPhysicalMarkingProduct (markedPhysicalEdgeSource u) ∨
      (p : ℕ) ∣ markedPhysicalMarkingProduct (markedPhysicalEdgeTarget u) := by
  have hp := Nat.prime_of_mem_primeFactors p.2
  have hpu := (Nat.mem_primeFactors.mp p.2).2.1
  obtain ⟨j,k,hjk⟩ := (markedPhysicalMarkingProduct_prime_dvd_iff hP u hp).mp hpu
  by_cases hk : k=Fin.last (M+1)
  · right
    apply (markedPhysicalMarkingProduct_prime_dvd_iff hP (markedPhysicalEdgeTarget u) hp).mpr
    refine ⟨j,Fin.last M,?_⟩
    simpa only [markedPhysicalEdgeTarget_last,hk] using hjk
  · left
    have hkv : k.val < M+1 := by
      have hne : k.val ≠ M+1 := fun h => hk (Fin.ext h)
      omega
    let k₀ : Fin (M+1) := ⟨k.val,hkv⟩
    have he : k₀.castSucc=k := Fin.ext rfl
    apply (markedPhysicalMarkingProduct_prime_dvd_iff hP (markedPhysicalEdgeSource u) hp).mpr
    refine ⟨j,k₀,?_⟩
    change (p : ℕ)=(u j k₀.castSucc : ℕ)
    rwa [he]

def markedPhysicalEdgeLineIncidence {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (u : MarkedPhysicalMarking P (M+2))
    (hS : Squarefree (markedPhysicalMarkingProduct u))
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u)))
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) : Prop :=
  (∀ p : (markedPhysicalMarkingProduct u).primeFactors,
    (p : ℕ) ∣ markedPhysicalMarkingProduct (markedPhysicalEdgeSource u) →
      markedPrimePositionLine (p : ℕ) (1,0) (by norm_num) = markedRootKernelTuple hS g p) ∧
  (∀ p : (markedPhysicalMarkingProduct u).primeFactors,
    (p : ℕ) ∣ markedPhysicalMarkingProduct (markedPhysicalEdgeTarget u) →
      markedPrimePositionLine (p : ℕ) z hz = markedRootKernelTuple hS g p)

def markedPhysicalEdgeAssignedLines {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (u : MarkedPhysicalMarking P (M+2))
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) : MarkedRootLineTuple (markedPhysicalMarkingProduct u) :=
  fun p => if (p : ℕ) ∣ markedPhysicalMarkingProduct (markedPhysicalEdgeSource u) then
    markedPrimePositionLine (p : ℕ) (1,0) (by norm_num) else markedPrimePositionLine (p : ℕ) z hz

theorem markedPhysicalEdgeLineIncidence_forces {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p ∈ P j → p.Prime) {M : ℕ}
    (u : MarkedPhysicalMarking P (M+2)) (hS : Squarefree (markedPhysicalMarkingProduct u))
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u)))
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (h : markedPhysicalEdgeLineIncidence u hS g z hz) :
    markedRootKernelTuple hS g=markedPhysicalEdgeAssignedLines u z hz := by
  funext p
  by_cases hs : (p : ℕ) ∣ markedPhysicalMarkingProduct (markedPhysicalEdgeSource u)
  · simp only [markedPhysicalEdgeAssignedLines,ite_eq_left hs]
    exact (h.1 p hs).symm
  · simp only [markedPhysicalEdgeAssignedLines,ite_eq_right hs]
    exact (h.2 p ((markedPhysicalEdge_prime_coverage hP u p).resolve_left hs)).symm

theorem markedPhysicalEdgeLineIncidence_iff_lift_hits {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (u : MarkedPhysicalMarking P (M+2))
    (hS : Squarefree (markedPhysicalMarkingProduct u))
    (root completion : ℤ × ℤ) (hdet : markedMinorIntegerDet root completion=1)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u)))
    (hred : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (markedPhysicalMarkingProduct u)))
      (markedPhysicalRootMatrix root completion hdet)=g)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    markedPhysicalEdgeLineIncidence u hS g z hz ↔
      (∀ p : (markedPhysicalMarkingProduct u).primeFactors,
        (p : ℕ) ∣ markedPhysicalMarkingProduct (markedPhysicalEdgeSource u) → ((p : ℕ) : ℤ) ∣ root.1) ∧
      (∀ p : (markedPhysicalMarkingProduct u).primeFactors,
        (p : ℕ) ∣ markedPhysicalMarkingProduct (markedPhysicalEdgeTarget u) →
          ((p : ℕ) : ℤ) ∣ (markedPhysicalRootLift root completion z).1) := by
  unfold markedPhysicalEdgeLineIncidence
  have hs (p : (markedPhysicalMarkingProduct u).primeFactors) :=
    markedPhysicalRootLift_kernel_hit hS root completion hdet g hred p (1,0) (by norm_num)
  have ht (p : (markedPhysicalMarkingProduct u).primeFactors) :=
    markedPhysicalRootLift_kernel_hit hS root completion hdet g hred p z hz
  simp only [markedPhysicalRootLift,Int.one_mul,Int.zero_mul,add_zero] at hs
  simp_rw [← hs,← ht]

end ArtinMatthews
