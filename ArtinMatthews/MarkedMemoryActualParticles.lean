module

public import ArtinMatthews.MarkedMemoryActualFibers
public import ArtinMatthews.MarkedMemoryHistoryTraceAnchors
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

/-! Each actual lineage address has a fixed band particle, with its
literal prime and initial/birth anchor. Anchor admissibility, itself
derived from nonzero weight, identifies it with every actual occurrence. -/
namespace ArtinMatthews
noncomputable section

theorem markedMemoryForgetBandParticle_injective {P : Finset Nat.Primes} :
    Function.Injective (markedMemoryForgetBandParticle (P := P)) := by
  rintro ⟨⟨p,hp⟩,l⟩ ⟨⟨q,hq⟩,m⟩ h
  change (⟨p,l⟩ : MarkedMemoryAnchoredPrime) = ⟨q,m⟩ at h
  cases h
  rfl

theorem markedMemoryPopulationPrime_mem_band {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (s : MarkedRawState P M B Z) (i : MarkedMemoryPopulationIndex s) :
    markedMemoryPopulationPrime s i ∈ P (markedMemoryPopulationGroup s i) := by
  rcases i with ⟨j,k⟩ | ⟨j,k⟩
  · exact (s.2.1 j k).2
  · exact (s.2.2.2 j k).1.2

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryActualFiber_prime_mem (j : J) (a : MarkedMemoryActualFiber hZ history j) :
    markedMemoryHistoryTraceAddressPrime hZ history a.1 ∈ P j := by
  obtain ⟨t,ht,i,hi⟩ := markedMemoryHistoryTraceAddress_present hZ history a.1
  have hp := markedMemoryHistoryTraceOrigin_prime hZ history t i
  have hg := markedMemoryHistoryTraceOrigin_group hZ history t i
  rw [hi] at hp hg
  have hgroup : markedMemoryPopulationGroup (markedMemoryHistoryTraceState hZ history t) i = j := hg.symm.trans a.2
  simpa only [hgroup, ← hp] using markedMemoryPopulationPrime_mem_band (markedMemoryHistoryTraceState hZ history t) i

def markedMemoryActualParticle (j : J) (a : MarkedMemoryActualFiber hZ history j) : MarkedRawParticle (P j) :=
  ⟨⟨(markedMemoryHistoryTraceAddressAnchor hZ history a.1).1,by
      rw [markedMemoryHistoryTraceAddressAnchor_prime]
      exact markedMemoryActualFiber_prime_mem hZ history j a⟩,
    (markedMemoryHistoryTraceAddressAnchor hZ history a.1).2⟩

theorem markedMemoryActualParticle_forget (j : J) (a : MarkedMemoryActualFiber hZ history j) :
    markedMemoryForgetBandParticle (markedMemoryActualParticle hZ history j a) =
      markedMemoryHistoryTraceAddressAnchor hZ history a.1 := rfl

theorem markedMemoryActualParticle_prime (j : J) (a : MarkedMemoryActualFiber hZ history j) :
    (markedMemoryActualParticle hZ history j a).1.1 = markedMemoryHistoryTraceAddressPrime hZ history a.1 :=
  markedMemoryHistoryTraceAddressAnchor_prime hZ history a.1

theorem markedMemoryActualParticle_pending (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (t : ℕ) (j : J) (k : Fin ((markedMemoryHistoryTraceState hZ history t).2.2.1.1 j : ℕ)) :
    markedMemoryActualParticle hZ history j (markedMemoryActualPendingIds hZ history t j k) =
      (markedMemoryHistoryTraceState hZ history t).2.2.2 j k := by
  apply markedMemoryForgetBandParticle_injective
  exact markedMemoryHistoryTraceOrigin_anchor hZ history ha t (Sum.inr ⟨j,k⟩)

theorem markedMemoryActualParticle_active (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (t : ℕ) (j : J) (k : Fin (pads+1)) :
    markedMemoryActualParticle hZ history j (markedMemoryActualActiveIds hZ history t j k) =
      markedRawAnchoredParticle (P j) ((markedMemoryHistoryTraceState hZ history t).2.1 j k)
        (markedMemoryHistoryTraceState hZ history t).1.1 (hZ _ (markedMemoryHistoryTraceState hZ history t).1.2) := by
  apply markedMemoryForgetBandParticle_injective
  exact markedMemoryHistoryTraceOrigin_anchor hZ history ha t (Sum.inl ⟨j,k⟩)

end
end ArtinMatthews
