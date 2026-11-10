module

public import ArtinMatthews.MarkedMemoryCappedPathConstruction
public import ArtinMatthews.MarkedMemoryIndependentBirthFactorials
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


set_option backward.privateInPublic true
@[expose] public section

/-! The ordered birth denominator on an actual capped path is exactly
the cardinality of its genuine birth-enumeration fiber. Summing this
fiber cancels the factorial for arbitrary signed coefficients. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [hA : ∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

omit hA in
theorem markedMemoryFinite_birthFactorials
    (f : MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n) :
    markedMemoryIndependentBirthFactorials hZ (markedMemoryFiniteTableau_toIndependent hZ f)=
      ∏ v : Fin (n+1),∏ j : J,((markedMemoryFiniteList_toList (f.1.births v j)).length.factorial:ℝ) := by
  unfold markedMemoryIndependentBirthFactorials
  change (∏ v : Fin (n+1),∏ j : J,((f.1.birthsAt (2*v.val) j).length.factorial:ℝ))=_
  simp only [MarkedMemoryFiniteTableauData.birthsAt_valid]

theorem markedMemoryEndpointBirthOrders_sum
    (E : MarkedMemoryEndpointData A P pads Z n) (w : ℝ) :
    (∑ _births : MarkedMemoryEndpointBirthOrders E,((w/(markedMemoryEndpointBirthFactorial E:ℝ):ℝ):ℂ))=(w:ℂ) := by
  cases Subsingleton.elim hA (fun j => Classical.decEq (A j))
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc := congrArg (fun m : ℕ => (m:ℂ)) (markedMemoryEndpointBirthOrders_card E)
  change (Fintype.card (MarkedMemoryEndpointBirthOrders E):ℂ)=(markedMemoryEndpointBirthFactorial E:ℂ) at hc
  rw [hc]
  change (markedMemoryEndpointBirthFactorial E:ℂ)*((w/(markedMemoryEndpointBirthFactorial E:ℝ):ℝ):ℂ)=(w:ℂ)
  push_cast
  have hn : (markedMemoryEndpointBirthFactorial E:ℂ)≠0 := by
    exact_mod_cast (markedMemoryEndpointBirthFactorial_pos E).ne'
  field_simp

variable (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)
  (hcap : MarkedMemoryPathCapacity hZ d c hc B)

theorem markedMemoryCappedPath_birthFactorials
    (births : MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ d c hc)) :
    markedMemoryIndependentBirthFactorials hZ
      (markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)=
        (markedMemoryEndpointBirthFactorial (markedMemoryPathEndpointData hZ d c hc):ℝ) := by
  rw [markedMemoryCappedPathIndependent,markedMemoryFinite_birthFactorials,
    markedMemoryCappedPathTableau_data]
  unfold markedMemoryEndpointBirthFactorial
  push_cast
  apply Finset.prod_congr rfl
  intro v _
  apply Finset.prod_congr rfl
  intro j _
  have hk := (markedMemoryFiniteListSet_card (births v j).1).symm.trans
    (congrArg Finset.card (births v j).2)
  change ((markedMemoryFiniteList_toList (births v j).1).length.factorial:ℝ)=_
  simp only [markedMemoryFiniteList_toList,List.length_ofFn]
  exact congrArg (fun m : ℕ => (m.factorial:ℝ)) hk

theorem markedMemoryCappedPath_birthFactorials_sum (w : ℝ) :
    (∑ births : MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ d c hc),
      ((w/markedMemoryIndependentBirthFactorials hZ
        (markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births):ℝ):ℂ))=(w:ℂ) := by
  have hs : (∑ births : MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ d c hc),
      ((w/markedMemoryIndependentBirthFactorials hZ
        (markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births):ℝ):ℂ))=
      ∑ _births : MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ d c hc),
        ((w/(markedMemoryEndpointBirthFactorial (markedMemoryPathEndpointData hZ d c hc):ℝ):ℝ):ℂ) := by
    apply Finset.sum_congr rfl
    intro births _
    rw [markedMemoryCappedPath_birthFactorials]
  exact hs.trans (markedMemoryEndpointBirthOrders_sum (markedMemoryPathEndpointData hZ d c hc) w)

end
end ArtinMatthews
