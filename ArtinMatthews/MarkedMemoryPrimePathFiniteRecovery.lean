module

public import ArtinMatthews.MarkedMemoryIndependentPathChoices
public import ArtinMatthews.MarkedMemoryActivePathFinite
public import ArtinMatthews.MarkedMemoryFiniteTableauRecovery
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

/-! Finite used-coordinate equality determines the entire prime-valued
active path and optional ghost choices. Total time tails play no role. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

theorem markedMemoryIndependentActivePath_congr
    {d e : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n}
    (h : d=e) (hd : Function.Injective (markedMemoryIndependentPrime hZ d))
    (he : Function.Injective (markedMemoryIndependentPrime hZ e)) :
    markedMemoryIndependentActivePath hZ d hd=markedMemoryIndependentActivePath hZ e he := by
  cases h
  rfl

variable (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hd : Function.Injective (markedMemoryIndependentPrime hZ d))

omit [∀ j,DecidableEq (A j)] in
include hd in
theorem markedMemoryIndependentPrime_restore_injective :
    Function.Injective (markedMemoryIndependentPrime hZ
      (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toFinite hZ d))) := hd

theorem markedMemoryIndependentActivePath_restore :
    markedMemoryIndependentActivePath hZ
      (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toFinite hZ d))
      (markedMemoryIndependentPrime_restore_injective hZ d hd)=markedMemoryIndependentActivePath hZ d hd := by
  apply markedMemoryActivePath_ext
  · funext v
    exact markedMemoryFinite_restore_position hZ d v.val (by omega)
  · funext v j
    apply Function.Embedding.ext
    intro k
    change (d.particle j
      ((markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toFinite hZ d)).activeId v.val j k)).1=_
    rw [markedMemoryFinite_restore_activeId hZ d v.val (by omega) j]
    rfl
  · funext v j
    change (d.particle j
      (((markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toFinite hZ d)).lifespan j).incoming (2*v.val+1))).1=_
    rw [markedMemoryFinite_restore_incoming hZ d v.val v.2 j]
    rfl
  · funext v j
    change (d.particle j
      (((markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toFinite hZ d)).lifespan j).outgoing (2*v.val+1))).1=_
    rw [markedMemoryFinite_restore_outgoing hZ d v.val v.2 j]
    rfl

omit hd [∀ j,DecidableEq (A j)] in
theorem markedMemoryIndependentPathChoices_restore :
    markedMemoryIndependentPathChoices hZ
      (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toFinite hZ d))=
        markedMemoryIndependentPathChoices hZ d := rfl

theorem markedMemoryIndependentActivePath_finite_eq
    (e : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
    (he : Function.Injective (markedMemoryIndependentPrime hZ e))
    (h : markedMemoryIndependent_toFinite hZ d=markedMemoryIndependent_toFinite hZ e) :
    markedMemoryIndependentActivePath hZ d hd=markedMemoryIndependentActivePath hZ e he := by
  have hh := markedMemoryIndependentActivePath_congr hZ
    (congrArg (markedMemoryFiniteTableau_toIndependent hZ) h)
    (markedMemoryIndependentPrime_restore_injective hZ d hd)
    (markedMemoryIndependentPrime_restore_injective hZ e he)
  exact (markedMemoryIndependentActivePath_restore hZ d hd).symm.trans
    (hh.trans (markedMemoryIndependentActivePath_restore hZ e he))

omit hd [∀ j,DecidableEq (A j)] in
theorem markedMemoryIndependentPathChoices_finite_eq
    (e : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
    (h : markedMemoryIndependent_toFinite hZ d=markedMemoryIndependent_toFinite hZ e) :
    markedMemoryIndependentPathChoices hZ d=markedMemoryIndependentPathChoices hZ e := by
  have hh := congrArg (markedMemoryIndependentPathChoices hZ)
    (congrArg (markedMemoryFiniteTableau_toIndependent hZ) h)
  exact (markedMemoryIndependentPathChoices_restore hZ d).symm.trans
    (hh.trans (markedMemoryIndependentPathChoices_restore hZ e))

end
end ArtinMatthews
