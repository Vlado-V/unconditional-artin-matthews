module

public import ArtinMatthews.MarkedMemoryCappedPathIndex
public import ArtinMatthews.MarkedMemoryPathCapacityExpansion
public import ArtinMatthews.MarkedMemoryActivePathFinite
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Remove the redundant initial active-list coordinate from the capped
decorated carrier. The remaining source condition is the actual initial
position; compatibility and the original pending capacity remain fields. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

structure MarkedMemoryCappedChoiceIndex (d : MarkedMemoryActivePathData P pads Z n) where
  choices : MarkedMemoryPathPrimeChoices (P := P) (n := n)
  compatible : MarkedMemoryPathChoicesCompatible d hZ choices
  capacity : MarkedMemoryPathCapacity hZ d choices compatible B

theorem markedMemoryCappedChoiceIndex_ext (d : MarkedMemoryActivePathData P pads Z n)
    {a b : MarkedMemoryCappedChoiceIndex (B := B) hZ d} (hc : a.choices=b.choices) : a=b := by
  cases a
  cases b
  cases hc
  rfl

instance markedMemoryCappedChoiceIndex_finite (d : MarkedMemoryActivePathData P pads Z n) :
    Finite (MarkedMemoryCappedChoiceIndex (B := B) hZ d) :=
  Finite.of_injective (fun c => c.choices) (fun _ _ h => markedMemoryCappedChoiceIndex_ext hZ d h)

instance markedMemoryCappedChoiceIndex_fintype (d : MarkedMemoryActivePathData P pads Z n) :
    Fintype (MarkedMemoryCappedChoiceIndex (B := B) hZ d) := Fintype.ofFinite _

def markedMemoryCappedChoiceSubtypeEquiv (d : MarkedMemoryActivePathData P pads Z n) :
    MarkedMemoryCappedChoiceIndex (B := B) hZ d ≃
      {c : {c : MarkedMemoryPathPrimeChoices (P := P) (n := n) //
        MarkedMemoryPathChoicesCompatible d hZ c} // MarkedMemoryPathCapacity hZ d c.1 c.2 B} where
  toFun c := ⟨⟨c.choices,c.compatible⟩,c.capacity⟩
  invFun c := ⟨c.1.1,c.1.2,c.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨⟨c,hc⟩,hcap⟩; rfl

theorem markedMemoryCappedChoiceIndex_sum {S : Type*} [AddCommMonoid S]
    (d : MarkedMemoryActivePathData P pads Z n)
    (f : MarkedMemoryPathPrimeChoices (P := P) (n := n) → S) :
    (∑ c : MarkedMemoryCappedChoiceIndex (B := B) hZ d,f c.choices)=
      ∑ c : {c : MarkedMemoryPathPrimeChoices (P := P) (n := n) //
        MarkedMemoryPathChoicesCompatible d hZ c},
        if MarkedMemoryPathCapacity hZ d c.1 c.2 B then f c.1 else 0 := by
  let e := markedMemoryCappedChoiceSubtypeEquiv (B := B) hZ d
  apply (Equiv.sum_comp e (fun c => f c.1.1)).trans
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter
    (fun c : {c : MarkedMemoryPathPrimeChoices (P := P) (n := n) //
      MarkedMemoryPathChoicesCompatible d hZ c} => MarkedMemoryPathCapacity hZ d c.1 c.2 B)) (by simp)
    (fun c => f c.1)).symm

theorem markedMemoryCappedChoiceIndex_weight_sum
    (d : MarkedMemoryActivePathData P pads Z n) (q : ℝ) :
    (∑ c : MarkedMemoryCappedChoiceIndex (B := B) hZ d,
      markedMemoryPathPrimeChoiceWeight hZ d q c.choices)=markedMemoryPathCappedChoiceSum hZ d q B :=
  markedMemoryCappedChoiceIndex_sum hZ d (markedMemoryPathPrimeChoiceWeight hZ d q)

abbrev MarkedMemoryCappedRawDecoratedIndex (z₀ : Z) :=
  Σ d : {d : MarkedMemoryActivePathData P pads Z n // d.position 0=z₀},
    Σ c : MarkedMemoryCappedChoiceIndex (B := B) hZ d.1,
      MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ d.1 c.choices c.compatible) ×
        (Fin n → J → Equiv.Perm (Fin pads))

instance markedMemoryCappedRawDecoratedIndex_fintype (z₀ : Z) :
    Fintype (MarkedMemoryCappedRawDecoratedIndex (P := P) (pads := pads) (B := B) (n := n) hZ z₀) := by infer_instance

def markedMemoryCappedSourceRawEquiv (z₀ : Z) :
    (Σ a : MarkedRawActive P (pads+1),
      MarkedMemoryCappedPathDecoratedIndex (n := n) hZ (markedMemoryBoundarySource (B := B) z₀ a)) ≃
      MarkedMemoryCappedRawDecoratedIndex (P := P) (pads := pads) (B := B) (n := n) hZ z₀ where
  toFun x := ⟨⟨x.2.1.path,congrArg (fun s : MarkedRawState P (pads+1) B Z => s.1) x.2.1.source⟩,
    ⟨⟨x.2.1.choices,x.2.1.compatible,x.2.1.capacity⟩,x.2.2⟩⟩
  invFun x := ⟨(fun j k => x.1.1.active 0 j k),
    ⟨⟨x.1.1,x.2.1.choices,x.2.1.compatible,x.2.1.capacity,
      congrArg (fun z => markedMemoryBoundarySource (B := B) z (fun j k => x.1.1.active 0 j k)) x.1.2⟩,x.2.2⟩⟩
  left_inv x := by
    rcases x with ⟨a,⟨⟨d,c,hc,hcap,hs⟩,births,order⟩⟩
    have ha : (fun j k => d.active 0 j k)=a :=
      congrArg (fun s : MarkedRawState P (pads+1) B Z => s.2.1) hs
    cases ha
    rfl
  right_inv x := by
    rcases x with ⟨⟨d,hd⟩,⟨⟨c,hc,hcap⟩,births,order⟩⟩
    rfl

theorem markedMemoryCappedSourceRaw_sum {S : Type*} [AddCommMonoid S] (z₀ : Z)
    (F : (Σ a : MarkedRawActive P (pads+1),
      MarkedMemoryCappedPathDecoratedIndex (n := n) hZ (markedMemoryBoundarySource (B := B) z₀ a)) → S) :
    (∑ x,F x)=∑ d : MarkedMemoryCappedRawDecoratedIndex (P := P) (pads := pads) (B := B) (n := n) hZ z₀,
      F ((markedMemoryCappedSourceRawEquiv (P := P) (pads := pads) (B := B) (n := n) hZ z₀).symm d) :=
  (Equiv.sum_comp (markedMemoryCappedSourceRawEquiv (P := P) (pads := pads) (B := B) (n := n) hZ z₀).symm F).symm

end
end ArtinMatthews
