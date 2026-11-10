module

public import ArtinMatthews.MarkedMemoryCappedPathConstruction
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

/-! A relabeling into the canonical used-prime carrier is forced by
the particle-prime field. Hence no extra label permutations remain in
the unlabelled capped path index. Birth enumerations remain literal. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (base : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (d : MarkedMemoryActivePathData P pads Z n) (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c) (hcap : MarkedMemoryPathCapacity hZ d c hc B)

theorem markedMemoryCappedLabel_prime
    (births : MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ d c hc))
    (e : (j : J) → A j ≃ MarkedMemoryPathUsedPrime d c j)
    (he : markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ e base)=
      markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births) (j : J) (a : A j) :
    (e j a).1=(base.particle j a).1 := by
  have hp := congrArg (fun f => f.1.particle j (e j a)) he
  have hl : (markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ e base)).1.particle j (e j a)=
      base.particle j a := by
    change base.particle j ((e j).symm (e j a))=base.particle j a
    rw [Equiv.symm_apply_apply]
  have hr := congrArg (fun f => f.particle j (e j a))
    (markedMemoryCappedPathTableau_data (B := B) hZ d c hc hcap births)
  exact (congrArg (fun p : MarkedRawParticle (P j) => p.1) (hl.symm.trans (hp.trans hr))).symm

theorem markedMemoryCappedLabel_unique
    (left right : MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ d c hc))
    (e f : (j : J) → A j ≃ MarkedMemoryPathUsedPrime d c j)
    (he : markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ e base)=
      markedMemoryCappedPathTableau (B := B) hZ d c hc hcap left)
    (hf : markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ f base)=
      markedMemoryCappedPathTableau (B := B) hZ d c hc hcap right) : e=f := by
  funext j
  apply Equiv.ext
  intro a
  apply Subtype.ext
  exact (markedMemoryCappedLabel_prime hZ base d c hc hcap left e he j a).trans
    (markedMemoryCappedLabel_prime hZ base d c hc hcap right f hf j a).symm

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryEndpointBirthOrders_decorate_injective
    (D : MarkedMemoryEndpointData A P pads Z n) :
    Function.Injective (markedMemoryEndpointDataDecorated D) := by
  intro a b h
  funext v j
  apply Subtype.ext
  exact congrArg (fun f => f.births v j) h

end
end ArtinMatthews
