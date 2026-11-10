module

public import ArtinMatthews.MarkedPhysicalMomentCopies
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

/-! Nonzero literal copy paths retain every physical good test at every
visit. Reverse entries retain the original oriented edge support. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
  (G : MarkedPhysicalState P (pads+1) Z → Prop)

local notation "State" => MarkedPhysicalState P (pads+1) Z
local notation "Slots" => J → Equiv.Perm (Fin (pads+1))
local notation "T" => markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q

theorem markedPhysicalMomentEdgeCopy_good (j : ℕ) (s t : State) (c : Slots × Slots)
    (h : markedPhysicalMomentEdgeCopy P hP V pads Z hZ ψ η d₀ Y Q q G j s t c≠0) :
    G s ∧ G t := by
  constructor
  · by_contra hs
    exact h (by simp only [markedPhysicalMomentEdgeCopy,ite_eq_right hs,zero_mul])
  · by_contra ht
    exact h (by simp only [markedPhysicalMomentEdgeCopy,ite_eq_right ht,mul_zero,zero_mul])

def markedPhysicalMomentCopySource (j : ℕ) (s t : State) (c : Slots × Slots) : State :=
  markedPhysicalSlotEquiv P (pads+1) Z c.1 (if j%2=0 then s else t)

def markedPhysicalMomentCopyTarget (j : ℕ) (s t : State) (c : Slots × Slots) : State :=
  markedPhysicalSlotEquiv P (pads+1) Z c.2 (if j%2=0 then t else s)

theorem markedPhysicalMomentEdgeCopy_edge_ne_zero (j : ℕ) (s t : State) (c : Slots × Slots)
    (h : markedPhysicalMomentEdgeCopy P hP V pads Z hZ ψ η d₀ Y Q q G j s t c≠0) :
    T (markedPhysicalMomentCopySource P pads Z j s t c)
      (markedPhysicalMomentCopyTarget P pads Z j s t c)≠0 := by
  intro hz
  apply h
  by_cases hj : j%2=0
  · simp only [markedPhysicalMomentCopySource,markedPhysicalMomentCopyTarget,hj,ite_true] at hz
    simp only [markedPhysicalMomentEdgeCopy,hj,ite_true,hz,mul_zero]
  · simp only [markedPhysicalMomentCopySource,markedPhysicalMomentCopyTarget,hj,ite_false] at hz
    simp only [markedPhysicalMomentEdgeCopy,hj,ite_false,hz,star_zero,mul_zero]

theorem markedPhysicalMomentCopies_all_good (n : ℕ) (hn : 0<n) (j : ℕ)
    (p : Fin (n+1) → State) (copies : Fin n → Slots × Slots)
    (h : (∏ v : Fin n, markedPhysicalMomentEdgeCopy P hP V pads Z hZ ψ η d₀ Y Q q G
      (j+v.val) (p v.castSucc) (p v.succ) (copies v))≠0) :
    ∀ v : Fin (n+1),G (p v) := by
  have he (v : Fin n) : markedPhysicalMomentEdgeCopy P hP V pads Z hZ ψ η d₀ Y Q q G
      (j+v.val) (p v.castSucc) (p v.succ) (copies v)≠0 :=
    (Finset.prod_ne_zero_iff.mp h) v (Finset.mem_univ v)
  intro v
  by_cases hv : v.val<n
  · let k : Fin n := ⟨v.val,hv⟩
    have hk : k.castSucc=v := Fin.ext rfl
    have hg := (markedPhysicalMomentEdgeCopy_good P hP V pads Z hZ ψ η d₀ Y Q q G
      _ _ _ _ (he k)).1
    simpa only [hk] using hg
  · let k : Fin n := ⟨n-1,by omega⟩
    have hk : k.succ=v := by apply Fin.ext; dsimp [k]; omega
    have hg := (markedPhysicalMomentEdgeCopy_good P hP V pads Z hZ ψ η d₀ Y Q q G
      _ _ _ _ (he k)).2
    simpa only [hk] using hg

end
end ArtinMatthews
