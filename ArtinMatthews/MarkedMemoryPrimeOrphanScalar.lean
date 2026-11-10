module

public import ArtinMatthews.MarkedMemoryPrimeIntervalScalar
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! A strict two-ended orphan has exactly the signed birth/death pair
and the damping at its actual intermediate inactive visits. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ} {L : Type*} (eta : Fin (N+1) → ℝ) (line : Fin (N+1) → L)

def markedMemoryOrphanVisitFactor (a b v : Fin (N+1)) : ℝ :=
  (if v=a then -eta a*markedLineHit line a (line a) else 1)*
    (if v=b then -eta b*markedLineHit line b (line a) else 1)*
      (if a<v ∧ v<b then markedMemoryPrimeDamping eta line a v else 1)

theorem markedMemoryPrimeIntervalVisitScalar_orphan (a b v : Fin (N+1)) (hab : a<b) :
    markedMemoryPrimeIntervalVisitScalar eta line ∅ (some a,some b) v=
      markedMemoryOrphanVisitFactor eta line a b v := by
  change
    ((if 2*a.val+1≤2*v.val ∧ 2*v.val≤2*b.val ∧ v∉(∅ : Finset (Fin (N+1))) then
        (if 2*b.val=2*v.val then -eta v*markedLineHit line v (line a)
          else 1-eta v*markedLineHit line v (line a)) else 1)*
      (if 2*a.val+1=2*v.val+1 ∧ 2*v.val+1≤2*b.val ∧ v∉(∅ : Finset (Fin (N+1))) then
        -eta v*markedLineHit line v (line a) else 1))=
      (if v=a then -eta a*markedLineHit line a (line a) else 1)*
        (if v=b then -eta b*markedLineHit line b (line a) else 1)*
          (if a<v ∧ v<b then 1-eta v*markedLineHit line v (line a) else 1)
  simp only [Finset.notMem_empty,not_false_eq_true,and_true]
  by_cases hva : v=a
  · subst v
    have hb : 2*a.val+1=2*a.val+1 ∧ 2*a.val+1≤2*b.val := by omega
    simp [hb,ne_of_lt hab]
  · by_cases hvb : v=b
    · subst v
      have hp : 2*a.val+1≤2*b.val ∧ 2*b.val≤2*b.val := by omega
      simp [hp,ne_of_gt hab]
    · have hp : (2*a.val+1≤2*v.val ∧ 2*v.val≤2*b.val) ↔ a<v ∧ v<b := by omega
      have hd : ¬2*b.val=2*v.val := by omega
      have hb : ¬(2*a.val+1=2*v.val+1 ∧ 2*v.val+1≤2*b.val) := by omega
      simp only [hp,ite_eq_right hb,ite_eq_right hva,ite_eq_right hvb,
        one_mul,mul_one]
      rw [ite_eq_right hd]


theorem markedMemoryOrphanVisitFactor_prod (a b : Fin (N+1)) (he : line a=line b) :
    (∏ v,markedMemoryOrphanVisitFactor eta line a b v)=
      eta a*eta b*(∏ v∈Finset.univ.filter (fun v => a<v ∧ v<b),
        (1-eta v*markedLineHit line v (line a))) := by
  simp only [markedMemoryOrphanVisitFactor]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  simp [Finset.prod_filter,markedMemoryPrimeDamping,markedLineHit,he]

theorem markedMemoryPrimeIntervalScalar_orphan (a b : Fin (N+1))
    (hab : a<b) (he : line a=line b) :
    markedMemoryPrimeIntervalScalar eta line ∅ (some a,some b)=
      eta a*eta b*(∏ v∈Finset.univ.filter (fun v => a<v ∧ v<b),
        (1-eta v*markedLineHit line v (line a))) := by
  unfold markedMemoryPrimeIntervalScalar
  simp_rw [markedMemoryPrimeIntervalVisitScalar_orphan eta line a b _ hab]
  exact markedMemoryOrphanVisitFactor_prod eta line a b he

end
end ArtinMatthews
