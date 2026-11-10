module

public import ArtinMatthews.GiantTwoSidedPatternKernel
public import ArtinMatthews.GiantTwoSidedRawSymmetrization
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Chronological signed dilation increments determine the actual
integer offsets of every visited positive physical state. A position
loop has zero total offset while the endpoint lists remain independent. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

def giantTwoSidedPathOffset {n : ℕ} (δ : Fin n → ℤ) (v : Fin (n+1)) : ℤ :=
  ∑ i ∈ (univ : Finset (Fin n)).filter (fun i => i.val < v.val),δ i

theorem giantTwoSidedPathOffset_zero {n : ℕ} (δ : Fin n → ℤ) :
    giantTwoSidedPathOffset δ 0=0 := by
  simp [giantTwoSidedPathOffset]

theorem giantTwoSidedPathOffset_succ {n : ℕ} (δ : Fin n → ℤ) (i : Fin n) :
    giantTwoSidedPathOffset δ i.succ=giantTwoSidedPathOffset δ i.castSucc+δ i := by
  classical
  have he : (univ : Finset (Fin n)).filter (fun j => j.val < i.succ.val) =
      insert i (univ.filter (fun j => j.val < i.castSucc.val)) := by
    ext j
    simp only [mem_filter,mem_univ,true_and,mem_insert,Fin.val_succ,Fin.val_castSucc]
    constructor
    · intro hj
      by_cases hji : j=i
      · exact Or.inl hji
      · exact Or.inr (by have hne : j.val≠i.val := fun heq => hji (Fin.ext heq); omega)
    · rintro (rfl | hj) <;> omega
  have hn : i∉(univ : Finset (Fin n)).filter (fun j => j.val < i.castSucc.val) := by simp
  rw [giantTwoSidedPathOffset,he,sum_insert hn,add_comm]
  rfl

def giantTwoSidedPatternPathIncrement {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)} {Z : Finset ℕ}
    (s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z)
    (π : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ) (i : Fin n) : ℤ :=
  step i*((giantTwoSidedPatternCopiedProduct (C i)
    (giantTwoSidedEndpointPermute (π i) (s i.castSucc)).val.2*
      giantTwoSidedPatternAuxiliaryProduct (aux i):ℕ):ℤ)

theorem giantTwoSidedPatternPath_position {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)} {Z : Finset ℕ}
    (s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z)
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (h : ∀ i,GiantTwoSidedPatternCondition (C i) (step i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)) (v : Fin (n+1)) :
    ((s v).val.1.val:ℤ)=((s 0).val.1.val:ℤ)+
      giantTwoSidedPathOffset (giantTwoSidedPatternPathIncrement s π aux step) v := by
  refine Fin.induction ?_ ?_ v
  · rw [giantTwoSidedPathOffset_zero,add_zero]
  · intro i ih
    have hs : ((s i.succ).val.1.val:ℤ)=((s i.castSucc).val.1.val:ℤ)+
        giantTwoSidedPatternPathIncrement s π aux step i := (h i).2.1
    rw [hs,ih,giantTwoSidedPathOffset_succ,add_assoc]

theorem giantTwoSidedPatternPath_return_iff {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)} {Z : Finset ℕ}
    (s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z)
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (h : ∀ i,GiantTwoSidedPatternCondition (C i) (step i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)) :
    (s (Fin.last n)).val.1.val=(s 0).val.1.val ↔
      giantTwoSidedPathOffset (giantTwoSidedPatternPathIncrement s π aux step) (Fin.last n)=0 := by
  have hp := giantTwoSidedPatternPath_position s π τ aux step h (Fin.last n)
  constructor
  · intro he
    rw [he] at hp
    omega
  · intro he
    rw [he,add_zero] at hp
    exact Int.ofNat.inj hp

end
end ArtinMatthews
