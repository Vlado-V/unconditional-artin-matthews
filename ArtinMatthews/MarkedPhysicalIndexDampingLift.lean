module

public import ArtinMatthews.MarkedPhysicalCoordinateIndexDamping
public import ArtinMatthews.MarkedPhysicalIndexRootGeometry
public import ArtinMatthews.MarkedPhysicalJointPrimeDamping
public import ArtinMatthews.MarkedPhysicalSourceBad
public import ArtinMatthews.MarkedPhysicalCoordinateIndexGuards
public import ArtinMatthews.MarkedPhysicalIndexGoodTransport
public import ArtinMatthews.MarkedPhysicalPathBonferroni
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

/-! The true physical loop and both endpoint dampings on a lifted path.
The loop is the literal final coordinate e1; the damping is the original
sqrt(q),q,...,sqrt(q) joint prime factor. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalCoordinateIndex_loop_iff
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {M n R S : ℕ}
    [NeZero S] {Z : Finset (ℤ × ℤ)} {U V : ℝ} (hU : 1<U) (hV : 1<V)
    (i : MarkedPhysicalCoordinateIndex P M n R)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V))
    (p : Fin (n+1) → MarkedPhysicalState P M Z)
    (hpos : ∀ v,(p v).1.1.1=markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
      (markedPhysicalCanonicalCompletion r) (markedPhysicalCoordinateIndexPath i.2.1 v)) :
    (p 0).1.1=(p (Fin.last n)).1.1 ↔ markedPhysicalCoordinateIndexPath i.2.1 (Fin.last n)=(1,0) := by
  have hfirst : (p 0).1.1.1=markedPhysicalCanonicalRootPosition r := by
    simpa only [markedPhysicalCoordinateIndexPath,Fin.cons_zero,markedPhysicalRootLift,
      Int.one_mul,Int.zero_mul,add_zero] using hpos 0
  constructor
  · intro h
    have hh := congrArg Subtype.val h
    rw [hfirst,hpos (Fin.last n)] at hh
    exact (markedPhysicalRootLift_eq_root_iff _ _ _ (markedPhysicalCanonicalCompletion_det hU hV r)).mp hh.symm
  · intro h
    apply Subtype.ext
    rw [hfirst,hpos (Fin.last n),h]
    simp [markedPhysicalRootLift]

theorem markedPhysicalCoordinateIndex_damping_joint
    {J : Type*} [Fintype J] [DecidableEq J] (P : J → Finset ℕ)
    {M n R S : ℕ} {Z : Finset (ℤ × ℤ)} {A B C D : ℝ}
    (i : MarkedPhysicalCoordinateIndex P M (n+1) R)
    (r : MarkedPhysicalCanonicalRoot S A B C D)
    (p : Fin (n+2) → MarkedPhysicalState P M Z) {q : ℝ} (hq : 0≤q)
    (hpos : ∀ v,(p v).1.1.1=markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
      (markedPhysicalCanonicalCompletion r) (markedPhysicalCoordinateIndexPath i.2.1 v))
    (hlab : ∀ v,(p v).1.2=i.1 v) :
    (∏ v : Fin (n+1),(markedPhysicalEndpointDamping P M q (p v.castSucc).1.1.1:ℂ)*
      (markedPhysicalEndpointDamping P M q (p v.succ).1.1.1:ℂ)) =
      (markedPhysicalJointPrimeWeight Finset.univ i.1 (markedMemoryVisitQ q (n+1))
        (fun v => (markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
          (markedPhysicalCanonicalCompletion r) (markedPhysicalCoordinateIndexPath i.2.1 v)).1.natAbs):ℂ) := by
  have hh := congrArg (fun a : ℝ => (a:ℂ)) (markedPhysicalPathDamping_joint P M Z hq n p)
  push_cast at hh
  simpa only [hpos,hlab] using hh

theorem markedPhysicalCoordinateIndex_lifted_damping
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x d₀ Y U V : ℝ)
    {n R S : ℕ} [NeZero S]
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) (n+1) R)
    (hR : 1≤R) (hU : 1<U) (hV : 1<V)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V))
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) V (2*V)) → ℤ × ℤ)
    (hw : ∀ a,markedMinorIntegerDet a.1 (w a)=1)
    (p : Fin (n+2) → MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x)
      (markedPhysicalPrimitiveBox U (16*U) V (2*V))) {q : ℝ} (hq : 0≤q)
    (hpos : ∀ v,(p v).1.1.1=markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
      (markedPhysicalCanonicalCompletion r) (markedPhysicalCoordinateIndexPath i.2.1 v))
    (hlab : ∀ v,(p v).1.2=i.1 v) :
    markedPhysicalMomentDampingPathTerm (fun j => markedLogPowerBand (e j) x)
      ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) V (2*V)) q
      (MarkedPhysicalActualGood e x d₀ Y w) (n+1) p =
      if markedPhysicalCoordinateIndexPath i.2.1 (Fin.last (n+1))=(1,0) ∧
          markedRootNormalizedPoint U V r.2.1∈markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V i hR then
        (markedPhysicalJointPrimeWeight Finset.univ i.1 (markedMemoryVisitQ q (n+1))
          (fun v => (markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
            (markedPhysicalCanonicalCompletion r) (markedPhysicalCoordinateIndexPath i.2.1 v)).1.natAbs):ℂ)
      else 0 := by
  have hc := and_congr (markedPhysicalCoordinateIndex_loop_iff hU hV i r p hpos)
    (markedPhysicalCoordinateIndex_good_path_iff e x d₀ Y U V i hR hU hV r w hw p hpos hlab)
  have hd := congrArg (fun a : ℝ => (a:ℂ)) (markedPhysicalPathDamping_joint
    (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) _ hq n p)
  push_cast at hd
  have hd' : (∏ v : Fin (n+1),
      (markedPhysicalEndpointDamping (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) q (p v.castSucc).1.1.1:ℂ)*
      (markedPhysicalEndpointDamping (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) q (p v.succ).1.1.1:ℂ)) =
      (markedPhysicalJointPrimeWeight Finset.univ i.1 (markedMemoryVisitQ q (n+1))
        (fun v => (markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
          (markedPhysicalCanonicalCompletion r) (markedPhysicalCoordinateIndexPath i.2.1 v)).1.natAbs):ℂ) := by
    simpa only [hpos,hlab] using hd
  unfold markedPhysicalMomentDampingPathTerm
  by_cases h : (p 0).1.1=(p (Fin.last (n+1))).1.1 ∧ ∀ v,MarkedPhysicalActualGood e x d₀ Y w (p v)
  · have hnew := hc.mp h
    rw [ite_eq_left h,ite_eq_left hnew]
    simpa only [markedPadSlots] using hd'
  · have hn : ¬(markedPhysicalCoordinateIndexPath i.2.1 (Fin.last (n+1))=(1,0) ∧
        markedRootNormalizedPoint U V r.2.1∈markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V i hR) :=
      fun hh => h (hc.mpr hh)
    rw [ite_eq_right h,ite_eq_right hn]

end ArtinMatthews
