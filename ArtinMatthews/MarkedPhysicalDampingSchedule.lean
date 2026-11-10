module

public import ArtinMatthews.MarkedPhysicalInactiveDamping
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The original two endpoint dampings per physical edge give exactly
sqrt(q) at the two path endpoints and q at each interior visit. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalInactivePrimeWeight_mul {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M : ℕ} (a : MarkedPhysicalMarking P M) (r s : ℝ) (u : ℕ) :
    markedPhysicalInactivePrimeWeight P a r u*markedPhysicalInactivePrimeWeight P a s u =
      markedPhysicalInactivePrimeWeight P a (r*s) u := by
  rw [markedPhysicalInactivePrimeWeight_pow,markedPhysicalInactivePrimeWeight_pow,
    markedPhysicalInactivePrimeWeight_pow,mul_pow]

theorem markedPhysicalInactivePrimeWeight_sqrt_sq {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M : ℕ} (a : MarkedPhysicalMarking P M) {q : ℝ} (hq : 0 ≤ q) (u : ℕ) :
    (markedPhysicalInactivePrimeWeight P a (Real.sqrt q) u)^2 = markedPhysicalInactivePrimeWeight P a q u := by
  rw [pow_two,markedPhysicalInactivePrimeWeight_mul,Real.mul_self_sqrt hq]

theorem marked_fin_edge_product (n : ℕ) (f : Fin (n+2) → ℝ) :
    (∏ v : Fin (n+1),f v.castSucc*f v.succ) =
      f 0*f (Fin.last (n+1))*(∏ v : Fin n,(f v.succ.castSucc)^2) := by
  rw [Finset.prod_mul_distrib,Fin.prod_univ_succ (fun v : Fin (n+1) => f v.castSucc),
    Fin.prod_univ_castSucc (fun v : Fin (n+1) => f v.succ)]
  simp only [Fin.castSucc_zero,Fin.succ_last,Fin.castSucc_succ]
  rw [Finset.prod_pow]
  ring

theorem marked_fin_visit_product (n : ℕ) (f : Fin (n+2) → ℝ) :
    (∏ v : Fin (n+2),if v.val=0 ∨ v.val=n+1 then f v else (f v)^2) =
      f 0*f (Fin.last (n+1))*(∏ v : Fin n,(f v.succ.castSucc)^2) := by
  rw [Fin.prod_univ_succ]
  rw [Fin.prod_univ_castSucc (fun v : Fin (n+1) =>
    if v.succ.val=0 ∨ v.succ.val=n+1 then f v.succ else (f v.succ)^2)]
  have hm (v : Fin n) : ¬(v.castSucc.succ.val=0 ∨ v.castSucc.succ.val=n+1) := by
    simp only [Fin.val_succ,Fin.val_castSucc]
    omega
  simp only [Fin.val_zero,true_or,ite_true,Fin.succ_last,Fin.val_last,or_true,ite_eq_right (hm _),
    Fin.castSucc_succ]
  ring

theorem markedPhysicalPathDamping_visit_schedule {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) {q : ℝ} (hq : 0 ≤ q)
    (n : ℕ) (path : Fin (n+2) → MarkedPhysicalState P M Z) :
    (∏ v : Fin (n+1),markedPhysicalEndpointDamping P M q (path v.castSucc).1.1.1*
      markedPhysicalEndpointDamping P M q (path v.succ).1.1.1) =
      ∏ v : Fin (n+2),markedPhysicalInactivePrimeWeight P (path v).1.2
        (markedMemoryVisitQ q (n+1) v) (path v).1.1.1.1.natAbs := by
  rw [marked_fin_edge_product n (fun v => markedPhysicalEndpointDamping P M q (path v).1.1.1),
    ← marked_fin_visit_product n (fun v => markedPhysicalEndpointDamping P M q (path v).1.1.1)]
  apply Finset.prod_congr rfl
  intro v _
  unfold markedMemoryVisitQ
  split_ifs
  · exact markedPhysicalEndpointDamping_eq_inactive P M q hq Z (path v)
  · rw [markedPhysicalEndpointDamping_eq_inactive P M q hq Z (path v),
      markedPhysicalInactivePrimeWeight_sqrt_sq P (path v).1.2 hq]

end ArtinMatthews
