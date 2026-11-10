module

public import ArtinMatthews.MarkedPhysicalActualLineMain
public import ArtinMatthews.MarkedPhysicalRootTargetReindex
public import ArtinMatthews.MarkedPhysicalEndpointState
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

/-! The literal physical endpoint divisibility tests imply exactly the
source/target residue-line event used by the Haar and discrepancy sums. -/

noncomputable section
namespace ArtinMatthews

theorem markedPhysical_prime_hit_of_labels {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p ∈ P j → p.Prime) {M S : ℕ}
    (a : MarkedPhysicalMarking P M) {n : ℤ}
    (ha : ∀ j k,((a j k : ℕ) : ℤ) ∣ n) (p : S.primeFactors)
    (hp : (p : ℕ) ∣ markedPhysicalMarkingProduct a) : ((p : ℕ) : ℤ) ∣ n := by
  obtain ⟨j,k,he⟩ := (markedPhysicalMarkingProduct_prime_dvd_iff hP a
    (Nat.prime_of_mem_primeFactors p.2)).mp hp
  simpa only [he] using ha j k

theorem markedPhysicalEdgeRootLineEvent_of_endpoints {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p ∈ P j → p.Prime) {M : ℕ}
    (u : MarkedPhysicalMarking P (M+2)) (hS : Squarefree (markedPhysicalMarkingProduct u))
    (root completion : ℤ × ℤ) (hdet : markedMinorIntegerDet root completion=1)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalMarkingProduct u)))
    (hred : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (markedPhysicalMarkingProduct u)))
      (markedPhysicalRootMatrix root completion hdet)=g)
    (z : ℤ × ℤ)
    (hs : MarkedPhysicalStateCondition root (markedPhysicalEdgeSource u))
    (ht : MarkedPhysicalStateCondition (markedPhysicalRootLift root completion z) (markedPhysicalEdgeTarget u)) :
    markedPhysicalEdgeRootLineEvent u hS g z := by
  have hz := (markedPhysicalRootLift_primitive_iff root completion z hdet).mp ht.1
  refine ⟨hz,(markedPhysicalEdgeLineIncidence_iff_lift_hits u hS root completion hdet g hred z hz).mpr ?_⟩
  exact ⟨fun p hp => markedPhysical_prime_hit_of_labels hP _ hs.2.2 p hp,
    fun p hp => markedPhysical_prime_hit_of_labels hP _ ht.2.2 p hp⟩

theorem markedPhysicalCanonicalRootLineEvent_of_endpoints {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p ∈ P j → p.Prime) {M : ℕ}
    (u : MarkedPhysicalMarking P (M+2)) (hS : Squarefree (markedPhysicalMarkingProduct u))
    [NeZero (markedPhysicalMarkingProduct u)] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D) (z : ℤ × ℤ)
    (hs : MarkedPhysicalStateCondition (markedPhysicalCanonicalRootPosition r) (markedPhysicalEdgeSource u))
    (ht : MarkedPhysicalStateCondition ((markedPhysicalCanonicalTargetEquiv hA hC r).symm z)
      (markedPhysicalEdgeTarget u)) :
    markedPhysicalEdgeRootLineEvent u hS r.1 z := by
  exact markedPhysicalEdgeRootLineEvent_of_endpoints hP u hS _ _
    (markedPhysicalCanonicalCompletion_det hA hC r) r.1
    (markedPhysicalCanonicalCompletion_reduction hA hC r) z hs ht

end ArtinMatthews
