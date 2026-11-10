module

public import ArtinMatthews.MarkedMemoryIndependentRecoveredCapacity
public import ArtinMatthews.MarkedMemoryCappedPathConstruction
public import ArtinMatthews.MarkedMemoryEndpointCanonicalRecovery
public import ArtinMatthews.MarkedMemoryIndependentPathRecovery
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

/-! Reverse extraction transports the original ordered birth batches
along the derived used-prime equivalence. Rebuilding recovers the whole
finite tableau, including each literal queue decoration. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hinj : Function.Injective (markedMemoryIndependentPrime hZ d))
  (hempty : ∀ j,(d.lifespan j).initial=[])
  (hterminal : ∀ j,markedMemoryIndependentQueue hZ d (2*n+1) j=[])
  (hn : MarkedMemoryBirthNormalized hZ d)
  (order : Fin n → J → Equiv.Perm (Fin pads))
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ (markedMemoryIndependentHistory hZ d order))

def markedMemoryIndependentCappedBirths :
    MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ
      (markedMemoryIndependentActivePath hZ d hinj) (markedMemoryIndependentPathChoices hZ d)
      (markedMemoryIndependentPathChoices_compatible hZ d hinj order hempty hterminal hn ha)) :=
  markedMemoryEndpointTransportBirths
    (markedMemoryIndependentPathRecovery_endpointData hZ d hinj hempty hterminal hn order ha)
    (markedMemoryEndpointOriginalBirths hZ (markedMemoryIndependent_toFinite hZ
      (markedMemoryIndependentRelabel hZ (markedMemoryIndependentUsedPrimeEquiv hZ d hinj hempty) d)))

theorem markedMemoryIndependentCappedBirths_rebuild :
    markedMemoryEndpointDataDecorated
      (markedMemoryPathEndpointData hZ (markedMemoryIndependentActivePath hZ d hinj)
        (markedMemoryIndependentPathChoices hZ d)
        (markedMemoryIndependentPathChoices_compatible hZ d hinj order hempty hterminal hn ha))
      (markedMemoryIndependentCappedBirths hZ d hinj hempty hterminal hn order ha)=
        (markedMemoryIndependent_toFinite hZ
          (markedMemoryIndependentRelabel hZ (markedMemoryIndependentUsedPrimeEquiv hZ d hinj hempty) d)).1 := by
  let rename := markedMemoryIndependentUsedPrimeEquiv hZ d hinj hempty
  let f := markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ rename d)
  have hi : ∀ j,markedMemoryFiniteList_toList (f.1.initial j)=[] := by
    intro j
    have he := markedMemoryFiniteData_initial hZ (markedMemoryIndependentRelabel hZ rename d) j
    have hj : ((markedMemoryIndependentRelabel hZ rename d).lifespan j).initial=[] := by
      change ((d.lifespan j).initial).map (rename j)=[]
      rw [hempty j,List.map_nil]
    exact he.trans hj
  have he := markedMemoryIndependentPathRecovery_endpointData hZ d hinj hempty hterminal hn order ha
  exact (markedMemoryEndpointDecorated_transport he (markedMemoryEndpointOriginalBirths hZ f)).trans
    (markedMemoryEndpointOriginal_rebuild hZ f hi)

theorem markedMemoryIndependentCappedTableau_recovery :
    markedMemoryCappedPathTableau (B := B) hZ (markedMemoryIndependentActivePath hZ d hinj)
      (markedMemoryIndependentPathChoices hZ d)
      (markedMemoryIndependentPathChoices_compatible hZ d hinj order hempty hterminal hn ha)
      (markedMemoryIndependentRecoveredCapacity hZ d hinj hempty hterminal hn order ha)
      (markedMemoryIndependentCappedBirths hZ d hinj hempty hterminal hn order ha)=
        markedMemoryIndependent_toFinite hZ
          (markedMemoryIndependentRelabel hZ (markedMemoryIndependentUsedPrimeEquiv hZ d hinj hempty) d) := by
  apply Subtype.ext
  exact (markedMemoryCappedPathTableau_data (B := B) hZ (markedMemoryIndependentActivePath hZ d hinj)
    (markedMemoryIndependentPathChoices hZ d)
    (markedMemoryIndependentPathChoices_compatible hZ d hinj order hempty hterminal hn ha)
    (markedMemoryIndependentRecoveredCapacity hZ d hinj hempty hterminal hn order ha)
    (markedMemoryIndependentCappedBirths hZ d hinj hempty hterminal hn order ha)).trans
      (markedMemoryIndependentCappedBirths_rebuild hZ d hinj hempty hterminal hn order ha)

end
end ArtinMatthews
