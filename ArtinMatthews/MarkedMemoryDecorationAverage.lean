module

public import ArtinMatthews.MarkedMemoryEndpointData
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

/-! Exact global averages over the constructed birth-order and copied-
slot-order fibers. Arbitrary decorated observables stay inside the
average. Its cardinalities are proved, including the empty cases. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*} [∀ j,Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (d : MarkedMemoryEndpointData A P pads Z n)

abbrev MarkedMemoryCopiedOrders := Fin n → J → Equiv.Perm (Fin pads)

def markedMemoryCopiedOrderCount (J : Type*) [Fintype J] (pads n : ℕ) : ℕ :=
  (pads.factorial^Fintype.card J)^n

theorem markedMemoryCopiedOrderCount_card :
    Fintype.card (MarkedMemoryCopiedOrders (J := J) (pads := pads) (n := n)) =
      markedMemoryCopiedOrderCount J pads n := by
  simp only [markedMemoryCopiedOrderCount,Fintype.card_fun,Fintype.card_perm,Fintype.card_fin]

theorem markedMemoryCopiedOrderCount_pos : 0 < markedMemoryCopiedOrderCount J pads n :=
  pow_pos (pow_pos (Nat.factorial_pos _) _) _

def markedMemoryDecorationAverage
    (F : MarkedMemoryEndpointBirthOrders d → MarkedMemoryCopiedOrders (J := J) (pads := pads) (n := n) → ℂ) : ℂ :=
  ((markedMemoryEndpointBirthFactorial d : ℂ)*(markedMemoryCopiedOrderCount J pads n : ℂ))⁻¹ *
    ∑ b : MarkedMemoryEndpointBirthOrders d,∑ o : MarkedMemoryCopiedOrders (J := J) (pads := pads) (n := n),F b o

theorem markedMemoryDecorationAverage_cancel_births
    (F : MarkedMemoryEndpointBirthOrders d → MarkedMemoryCopiedOrders (J := J) (pads := pads) (n := n) → ℂ) :
    (∑ b : MarkedMemoryEndpointBirthOrders d,∑ o : MarkedMemoryCopiedOrders (J := J) (pads := pads) (n := n),F b o) /
      (markedMemoryEndpointBirthFactorial d : ℂ) =
    (markedMemoryCopiedOrderCount J pads n : ℂ) * markedMemoryDecorationAverage d F := by
  have hb : (markedMemoryEndpointBirthFactorial d : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (markedMemoryEndpointBirthFactorial_pos d))
  have hc : (markedMemoryCopiedOrderCount J pads n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (markedMemoryCopiedOrderCount_pos (J := J) (pads := pads) (n := n)))
  unfold markedMemoryDecorationAverage
  field_simp

theorem markedMemoryDecorationAverage_const (c : ℂ) :
    markedMemoryDecorationAverage d (fun _ _ => c)=c := by
  have hb : (markedMemoryEndpointBirthFactorial d : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (markedMemoryEndpointBirthFactorial_pos d))
  have hc : (markedMemoryCopiedOrderCount J pads n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (markedMemoryCopiedOrderCount_pos (J := J) (pads := pads) (n := n)))
  unfold markedMemoryDecorationAverage
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    markedMemoryEndpointBirthOrders_card,markedMemoryCopiedOrderCount_card]
  change ((markedMemoryEndpointBirthFactorial d : ℂ)*(markedMemoryCopiedOrderCount J pads n : ℂ))⁻¹ *
    ((markedMemoryEndpointBirthFactorial d : ℂ)*((markedMemoryCopiedOrderCount J pads n : ℂ)*c))=c
  field_simp

end
end ArtinMatthews
