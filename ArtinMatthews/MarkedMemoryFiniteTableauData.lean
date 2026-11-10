module

public import ArtinMatthews.MarkedMemoryFiniteLists
public import ArtinMatthews.MarkedMinorArcRawState
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Finite storage for a lifespan tableau. No Nat-indexed function or
unbounded list is stored. Total functions below are canonical extensions
of finite coordinates, not additional summation data. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*}

@[ext] structure MarkedMemoryFiniteTableauData [Fintype J] (A : J → Type*) [∀ j,Fintype (A j)]
    (P : J → Finset Nat.Primes) (pads : ℕ) (Z : Finset (ℤ × ℤ)) (n : ℕ) where
  first : (j : J) → A j → Fin (2*n+2)
  last : (j : J) → A j → Fin (2*n+2)
  active : Fin (2*n+2) → (j : J) → Finset (A j)
  initial : (j : J) → MarkedMemoryFiniteList (A j)
  births : Fin (n+1) → (j : J) → MarkedMemoryFiniteList (A j)
  incoming : Fin n → (j : J) → A j
  outgoing : Fin n → (j : J) → A j
  position : Fin (n+1) → Z
  activeId : Fin (n+1) → (j : J) → Fin (pads+1) ↪ A j
  particle : (j : J) → A j → MarkedRawParticle (P j)

variable [Fintype J] {A : J → Type*} [∀ j,Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}

instance markedMemoryFiniteTableauData_finite : Finite (MarkedMemoryFiniteTableauData A P pads Z n) := by
  classical
  let encode := fun d : MarkedMemoryFiniteTableauData A P pads Z n =>
    (d.first,d.last,d.active,d.initial,d.births,d.incoming,d.outgoing,d.position,d.activeId,d.particle)
  have hi : Function.Injective encode := by
    intro a b h
    have hh : a.first=b.first ∧ a.last=b.last ∧ a.active=b.active ∧ a.initial=b.initial ∧
        a.births=b.births ∧ a.incoming=b.incoming ∧ a.outgoing=b.outgoing ∧
        a.position=b.position ∧ a.activeId=b.activeId ∧ a.particle=b.particle := by
      simpa only [encode,Prod.mk.injEq] using h
    rcases hh with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀⟩
    exact MarkedMemoryFiniteTableauData.ext h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀
  exact Finite.of_injective encode hi

instance markedMemoryFiniteTableauData_fintype : Fintype (MarkedMemoryFiniteTableauData A P pads Z n) := Fintype.ofFinite _

namespace MarkedMemoryFiniteTableauData

variable (d : MarkedMemoryFiniteTableauData A P pads Z n)

def firstAt (j : J) (a : A j) : ℕ := (d.first j a).val
def lastAt (j : J) (a : A j) : ℕ := (d.last j a).val

def activeAt (t : ℕ) (j : J) (a : A j) : Prop :=
  if h : t < 2*n+2 then a ∈ d.active ⟨t,h⟩ j else False

def initialAt (j : J) : List (A j) := markedMemoryFiniteList_toList (d.initial j)

def birthsAt (t : ℕ) (j : J) : List (A j) :=
  if h : t % 2 = 0 ∧ t/2 ≤ n then
    markedMemoryFiniteList_toList (d.births ⟨t/2,by omega⟩ j) else []

def incomingAt (t : ℕ) (j : J) : A j :=
  if h : t % 2 = 1 ∧ t/2 < n then d.incoming ⟨t/2,h.2⟩ j
  else d.activeId ⟨0,by omega⟩ j ⟨0,by omega⟩

def outgoingAt (t : ℕ) (j : J) : A j :=
  if h : t % 2 = 1 ∧ t/2 < n then d.outgoing ⟨t/2,h.2⟩ j
  else d.activeId ⟨0,by omega⟩ j ⟨0,by omega⟩

def positionAt (v : ℕ) : Z := d.position ⟨min v n,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def activeIdAt (v : ℕ) (j : J) : Fin (pads+1) ↪ A j :=
  d.activeId ⟨min v n,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ j

def pendingAt (t : ℕ) (j : J) : Finset (A j) := by
  classical
  exact Finset.univ.filter (fun a => d.firstAt j a ≤ t ∧ t ≤ d.lastAt j a ∧ ¬d.activeAt t j a)

@[simp] theorem activeAt_valid (t : Fin (2*n+2)) (j : J) (a : A j) :
    d.activeAt t.val j a ↔ a ∈ d.active t j := by simp [activeAt,t.isLt]

@[simp] theorem birthsAt_valid (v : Fin (n+1)) (j : J) :
    d.birthsAt (2*v.val) j = markedMemoryFiniteList_toList (d.births v j) := by
  simp [birthsAt,show v.val ≤ n by omega]

@[simp] theorem incomingAt_valid (v : Fin n) (j : J) :
    d.incomingAt (2*v.val+1) j = d.incoming v j := by
  simp [incomingAt,Nat.add_div,v.isLt]

@[simp] theorem outgoingAt_valid (v : Fin n) (j : J) :
    d.outgoingAt (2*v.val+1) j = d.outgoing v j := by
  simp [outgoingAt,Nat.add_div,v.isLt]

@[simp] theorem positionAt_valid (v : Fin (n+1)) : d.positionAt v.val = d.position v := by
  simp [positionAt,Nat.min_eq_left (show v.val ≤ n by omega)]

@[simp] theorem activeIdAt_valid (v : Fin (n+1)) (j : J) :
    d.activeIdAt v.val j = d.activeId v j := by
  simp [activeIdAt,Nat.min_eq_left (show v.val ≤ n by omega)]

end MarkedMemoryFiniteTableauData
end
end ArtinMatthews
