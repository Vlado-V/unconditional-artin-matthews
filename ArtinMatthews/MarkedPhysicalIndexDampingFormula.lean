module

public import ArtinMatthews.MarkedPhysicalCoordinateIndexDamping
public import ArtinMatthews.MarkedPhysicalIndexRootGeometry
public import ArtinMatthews.MarkedPhysicalJointPrimeDamping
public import ArtinMatthews.MarkedPhysicalSourceBad
public import ArtinMatthews.MarkedPhysicalIndexDampingLift
public import ArtinMatthews.MarkedPhysicalIndexGoodTransport
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact pointwise zero-extension formula for the original physical
index damping on the full box. Validity, terminal position and every
actual good test are kept before the joint q factor is exposed. -/

noncomputable section
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

theorem markedPhysicalMomentLength_pos {x : ℝ} (hx : 1 < x) : 0 < markedMemoryMomentLength x := by
  unfold markedMemoryMomentLength
  exact Nat.mul_pos (by norm_num) (Nat.ceil_pos.mpr
    (div_pos (Real.rpow_pos_of_pos (Real.log_pos hx) _) (by norm_num)))

def markedPhysicalIndexLiftedPosition {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M n R S : ℕ} {U V : ℝ}
    (i : MarkedPhysicalCoordinateIndex P M n R)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) (v : Fin (n+1)) : ℤ × ℤ :=
  markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r)
    (markedPhysicalCoordinateIndexPath i.2.1 v)

def MarkedPhysicalIndexRootValid {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M n R S : ℕ} {U V : ℝ}
    (i : MarkedPhysicalCoordinateIndex P M n R)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) : Prop :=
  ∀ v,MarkedPhysicalStateCondition (markedPhysicalIndexLiftedPosition i r v) (i.1 v)

theorem markedPhysicalIndexLiftedPosition_eq_cons {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M n R S : ℕ} {U V : ℝ}
    (i : MarkedPhysicalCoordinateIndex P M n R)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) :
    markedPhysicalIndexLiftedPosition i r =
      Fin.cons (markedPhysicalCanonicalRootPosition r)
        (fun v => markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
          (markedPhysicalCanonicalCompletion r) (i.2.1 v).1) := by
  funext v
  cases v using Fin.cases with
  | zero => simp [markedPhysicalIndexLiftedPosition,markedPhysicalCoordinateIndexPath,markedPhysicalRootLift]
  | succ k => rfl

theorem markedPhysicalCoordinateIndexDamping_formula
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x d₀ Y U V : ℝ)
    {n R S : ℕ} [NeZero S] (hn : 0<n)
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) (hU : 1<U) (hV : 1<V)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V))
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) V (2*V)) → ℤ × ℤ)
    (hw : ∀ a,markedMinorIntegerDet a.1 (w a)=1) {q : ℝ} (hq : 0≤q) :
    markedPhysicalCoordinateIndexDamping (fun j => markedLogPowerBand (e j) x)
      ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) V (2*V)) q
      (MarkedPhysicalActualGood e x d₀ Y w) i r =
      if MarkedPhysicalIndexRootValid i r ∧
          markedPhysicalCoordinateIndexPath i.2.1 (Fin.last n)=(1,0) ∧
          markedRootNormalizedPoint U V r.2.1∈markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V i hR then
        (markedPhysicalJointPrimeWeight Finset.univ i.1 (markedMemoryVisitQ q n)
          (fun v => (markedPhysicalIndexLiftedPosition i r v).1.natAbs):ℂ)
      else 0 := by
  cases n with
  | zero => omega
  | succ n =>
    unfold markedPhysicalCoordinateIndexDamping markedPhysicalPathCoordinateTerm
    rw [← markedPhysicalIndexLiftedPosition_eq_cons i r]
    by_cases hb : ∀ v,markedPhysicalIndexLiftedPosition i r v∈markedPhysicalPrimitiveBox U (16*U) V (2*V)
    · rw [markedPhysicalPositionPathExtend,dite_eq_left hb]
      let pos : MarkedPhysicalPositionPath (markedPhysicalPrimitiveBox U (16*U) V (2*V)) (n+1) :=
        fun v => ⟨markedPhysicalIndexLiftedPosition i r v,hb v⟩
      change @markedPhysicalPathArrayExtend J (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (n+1) (markedPhysicalPrimitiveBox U (16*U) V (2*V))
        (markedPhysicalMomentDampingPathTerm (fun j => markedLogPowerBand (e j) x)
          ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) V (2*V)) q
          (MarkedPhysicalActualGood e x d₀ Y w) (n+1)) pos i.1 = _
      by_cases ha : MarkedPhysicalPathArrayValid pos i.1
      · unfold markedPhysicalPathArrayExtend
        rw [dite_eq_left ha]
        let p := markedPhysicalPathOfArrays pos i.1 ha
        have hp (v) : (p v).1.1.1=markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
            (markedPhysicalCanonicalCompletion r) (markedPhysicalCoordinateIndexPath i.2.1 v) := rfl
        have hl (v) : (p v).1.2=i.1 v := rfl
        have hf := markedPhysicalCoordinateIndex_lifted_damping e x d₀ Y U V i hR hU hV r w hw p hq hp hl
        have hv : MarkedPhysicalIndexRootValid i r := ha
        rw [hf]
        simp only [hv,true_and,markedPhysicalIndexLiftedPosition]
      · unfold markedPhysicalPathArrayExtend
        rw [dite_eq_right ha]
        have hv : ¬MarkedPhysicalIndexRootValid i r := ha
        simp only [hv,false_and,ite_false]
    · rw [markedPhysicalPositionPathExtend,dite_eq_right hb]
      have hg : markedRootNormalizedPoint U V r.2.1∉markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V i hR := by
        intro hg
        apply hb
        intro v
        exact ((markedPhysicalCoordinateIndexGoodSet_mem_iff e x d₀ Y U V i hR hU hV r).mp hg v).1
      simp only [hg,and_false,ite_false]

end ArtinMatthews
