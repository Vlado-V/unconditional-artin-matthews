module

public import ArtinMatthews.MarkedMemoryIndependentIntervalCompatible
public import ArtinMatthews.MarkedMemoryNormalizedEndpointWeight
public import ArtinMatthews.MarkedMemoryPrimeIntervalScalar
public import ArtinMatthews.MarkedMemoryIndependentIntervalUsed
public import ArtinMatthews.MarkedMemoryPrimeChoiceScalar
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

/-! Actual normalized independent endpoint scalars are exactly the
primewise line-choice coefficients. The interval, active visits and
reference line are recovered from genuine local data. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hempty : ∀ j,(d.lifespan j).initial=[])
  (hterminal : ∀ j,markedMemoryIndependentQueue hZ d (2*n+1) j=[])
  (hn : MarkedMemoryBirthNormalized hZ d)

local notation "V" j:max a:max => markedMemoryIndependentIdentityVisits hZ d j a
local notation "C" j:max a:max => markedMemoryIndependentIntervalChoice hZ d j a
local notation "line" j:max a:max => markedMemoryIndependentPositionLines hZ d j a

include hempty hterminal hn in
theorem markedMemoryIndependentEndpointScalar_interval (q : ℝ) (j : J) (a : A j) :
    markedMemoryIndependentEndpointScalar hZ d q ⟨j,a⟩=
      markedMemoryPrimeIntervalScalar (markedMemoryEta q n) (line j a) (V j a) (C j a) := by
  have hv : markedMemoryPrimeBirthVisit (V j a) (C j a)=markedMemoryIndependentBirthVertex hZ d j a := by
    apply Fin.ext
    rw [markedMemoryPrimeBirthVisit_eq_first_div,markedMemoryIndependentIntervalChoice_first hZ d hempty j a]
    rfl
  have hb : (line j a) (markedMemoryPrimeBirthVisit (V j a) (C j a))=(d.particle j a).2 := by
    rw [hv]
    exact (markedMemoryIndependent_birth_line hZ d hn j a).symm
  unfold markedMemoryIndependentEndpointScalar markedMemoryPrimeIntervalScalar
  apply Finset.prod_congr rfl
  intro v _
  simp only [markedMemoryPrimeIntervalVisitScalar,markedMemoryIndependentIntervalChoice_first hZ d hempty j a,
    markedMemoryIndependentIntervalChoice_last hZ d hterminal j a,
    markedMemoryIndependentIdentityVisits_mem]
  simp only [hb]
  rfl

variable (order : Fin n → J → Equiv.Perm (Fin pads))
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ (markedMemoryIndependentHistory hZ d order))

include hempty hterminal hn order ha in
theorem markedMemoryIndependentChoiceWeight_scalar (q atom : ℝ) (j : J) (a : A j) :
    markedMemoryPrimeLifespanChoiceWeight (markedMemoryEta q n) (line j a) (V j a) atom (C j a)=
      atom*markedMemoryIndependentEndpointScalar hZ d q ⟨j,a⟩ := by
  rw [markedMemoryPrimeChoiceWeight_used_interval (markedMemoryEta q n) (line j a) (V j a) atom (C j a)
    (markedMemoryIndependent_interval_compatible hZ d order hempty hterminal hn ha j a)
    (markedMemoryIndependent_interval_used hZ d hempty j a),
    ← markedMemoryIndependentEndpointScalar_interval hZ d hempty hterminal hn q j a]

end
end ArtinMatthews
