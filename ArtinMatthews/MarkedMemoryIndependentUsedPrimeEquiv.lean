module

public import ArtinMatthews.MarkedMemoryIndependentPathChoices
public import ArtinMatthews.MarkedMemoryIndependentIntervalUsed
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Actual identities are exactly the primes used by the recovered
primewise choices. This bandwise equivalence is constructed from the
injective numeric label map and local empty-initial queue incidence;
no coverage, cardinality or bijection premise is supplied. -/
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

local notation "path" => markedMemoryIndependentActivePath hZ d hinj
local notation "choices" => markedMemoryIndependentPathChoices hZ d
local notation "Used" => MarkedMemoryPathUsedPrime path choices
local notation "emb" => markedMemoryIndependentBandPrimeEmbedding hZ d hinj

def markedMemoryIndependentUsedPrimeEquiv (j : J) : A j ≃ Used j :=
  Equiv.ofBijective
    (fun a => ⟨(d.particle j a).1,by
      rw [markedMemoryIndependentPathVisits_at hZ d hinj j a,
        markedMemoryIndependentPathChoices_at hZ d hinj j a]
      exact markedMemoryIndependent_interval_used hZ d hempty j a⟩)
    ⟨by
      intro a b he
      exact (emb j).injective (congrArg Subtype.val he),
     by
      intro p
      by_cases hp : ∃ a : A j,(d.particle j a).1=p.1
      · obtain ⟨a,ha⟩ := hp
        exact ⟨a,Subtype.ext ha⟩
      · have hh := p.2
        rw [markedMemoryIndependentPathVisits_absent hZ d hinj j p.1 hp] at hh
        simp only [markedMemoryIndependentPathChoices,dite_eq_right hp,
          MarkedMemoryPrimeLifespanUsed,Finset.not_nonempty_empty,false_or,ne_eq,not_true_eq_false] at hh
        ⟩

theorem markedMemoryIndependentUsedPrimeEquiv_prime (j : J) (a : A j) :
    (markedMemoryIndependentUsedPrimeEquiv hZ d hinj hempty j a).1=(d.particle j a).1 := rfl

include hinj hempty in
theorem markedMemoryIndependent_card_le_band (j : J) : Fintype.card (A j)≤(P j).card := by
  rw [Fintype.card_congr (markedMemoryIndependentUsedPrimeEquiv hZ d hinj hempty j)]
  exact (Fintype.card_subtype_le _).trans (by simp)

end
end ArtinMatthews
