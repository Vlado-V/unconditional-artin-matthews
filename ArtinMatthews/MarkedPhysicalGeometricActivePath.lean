module

public import ArtinMatthews.MarkedPhysicalMomentGeometric
public import ArtinMatthews.MarkedMemoryActivePathData
public import ArtinMatthews.MarkedPhysicalSlotSupport
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

/-! A supported literal physical copy path supplies the actual active
prime path used by the independent-line/history reconstruction. Exchange
and fresh-prime exclusion are derived from the physical coefficient. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)

local notation "State" => MarkedPhysicalState P (pads+1) Z
local notation "Slots" => J → Equiv.Perm (Fin (pads+1))
local notation "Bands" => fun j => markedRawPrimeBand (P j)

theorem markedPhysicalGeometricCopy_exchange (j : ℕ) (s t : State) (c : Slots × Slots)
    (h : markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q j s t c≠0) :
    let a := (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1
    let b := (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1
    (∀ i,¬∃ k,a i k=b i (c.2 i (Fin.last pads))) ∧
      (∀ i x,(∃ k,b i k=x) ↔
        ((∃ k,a i k=x) ∧ x≠a i (c.1 i (Fin.last pads))) ∨ x=b i (c.2 i (Fin.last pads))) := by
  by_cases hj : j%2=0
  · apply markedPhysicalPermutedEdge_exchange P hP V pads Z hZ ψ η d₀ Y Q q s t c.1 c.2
    intro hz
    exact h (by simp only [markedPhysicalMomentGeometricCopy,hj,ite_true,hz,mul_zero])
  · apply markedPhysicalPermutedEdge_exchange P hP V pads Z hZ
      (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u)) d₀ Y Q q s t c.1 c.2
    intro hz
    exact h (by simp only [markedPhysicalMomentGeometricCopy,hj,ite_false,hz,mul_zero])

def markedPhysicalSupportedActivePath (n : ℕ) (p : Fin (n+1) → State)
    (copies : Fin n → Slots × Slots)
    (hsupport : ∀ v : Fin n,markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q
      v.val (p v.castSucc) (p v.succ) (copies v)≠0) :
    MarkedMemoryActivePathData Bands pads Z n where
  position v := (p v).1.1
  active v j :=
    { toFun := fun k => (markedPhysicalStateToRaw P hP (pads+1) Z (p v)).2.1 j k
      inj' := markedPhysicalStateToRaw_distinct P hP (pads+1) Z (p v) j }
  incoming v j := (markedPhysicalStateToRaw P hP (pads+1) Z (p v.succ)).2.1 j
    ((copies v).2 j (Fin.last pads))
  outgoing v j := (markedPhysicalStateToRaw P hP (pads+1) Z (p v.castSucc)).2.1 j
    ((copies v).1 j (Fin.last pads))
  outgoing_present v j := ⟨(copies v).1 j (Fin.last pads),rfl⟩
  incoming_present v j := ⟨(copies v).2 j (Fin.last pads),rfl⟩
  incoming_not_source v j :=
    (markedPhysicalGeometricCopy_exchange P hP V pads Z hZ ψ η d₀ Y Q q
      _ _ _ _ (hsupport v)).1 j
  exchange v j x :=
    (markedPhysicalGeometricCopy_exchange P hP V pads Z hZ ψ η d₀ Y Q q
      _ _ _ _ (hsupport v)).2 j x

variable (n : ℕ) (p : Fin (n+1) → MarkedPhysicalState P (pads+1) Z)
  (copies : Fin n → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))))
  (hsupport : ∀ v : Fin n,markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q
    v.val (p v.castSucc) (p v.succ) (copies v)≠0)

local notation "D" => markedPhysicalSupportedActivePath P hP V pads Z hZ ψ η d₀ Y Q q n p copies hsupport

theorem markedPhysicalSupportedActivePath_position (v : Fin (n+1)) :
    (D).position v=(p v).1.1 := rfl

theorem markedPhysicalSupportedActivePath_active (v : Fin (n+1)) (j : J) (k : Fin (pads+1)) :
    (D).active v j k=(markedPhysicalStateToRaw P hP (pads+1) Z (p v)).2.1 j k := rfl

theorem markedPhysicalSupportedActivePath_outgoing (v : Fin n) (j : J) :
    (D).outgoing v j=(markedPhysicalStateToRaw P hP (pads+1) Z (p v.castSucc)).2.1 j
      ((copies v).1 j (Fin.last pads)) := rfl

theorem markedPhysicalSupportedActivePath_incoming (v : Fin n) (j : J) :
    (D).incoming v j=(markedPhysicalStateToRaw P hP (pads+1) Z (p v.succ)).2.1 j
      ((copies v).2 j (Fin.last pads)) := rfl

theorem markedPhysicalSupportedActivePath_raw_vertex (v : Fin (n+1)) :
    ((D).position v,(fun j k => (D).active v j k,markedPhysicalEmptyMemory Bands)) =
      markedPhysicalStateToRaw P hP (pads+1) Z (p v) := rfl

theorem markedPhysicalSupportedActivePath_loop
    (hloop : (p 0).1.1=(p (Fin.last n)).1.1) : (D).position 0=(D).position (Fin.last n) := hloop

theorem markedPhysicalSupportedActivePath_active_divides (v : Fin (n+1)) (j : J) (k : Fin (pads+1)) :
    ((((D).active v j k).1:ℕ):ℤ)∣((D).position v).1.1 :=
  (p v).2.2.2 j k

end
end ArtinMatthews
