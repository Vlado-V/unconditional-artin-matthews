module

public import ArtinMatthews.MarkedMemoryLifespanEndpointSums
public import ArtinMatthews.MarkedMemoryHistoryLifespanScalarLines
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

/-! Optional endpoint sums on the actual active-visit set of an indexed
trace identity. No identification of different numeric prime occurrences
is used, and no history/tableau coverage theorem is a premise. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

def markedMemoryHistoryScalarActiveVisits (a : MarkedMemoryHistoryTraceAddress hZ history) :
    Finset (Fin (n+1)) :=
  Finset.univ.filter (fun v => ∃ band k,
    markedMemoryHistoryGhostSourceOrigin hZ history v (Sum.inl ⟨band,k⟩) = a)

def markedMemoryHistoryScalarVertexAtom (q : ℝ) (a : MarkedMemoryHistoryTraceAddress hZ history)
    (v : Fin (n+1)) : ℝ :=
  markedMemoryEta q n v * markedMemoryHistoryAddressLineHit hZ history a v

def markedMemoryHistoryIndexedProjectiveFactor (q : ℝ)
    (a : MarkedMemoryHistoryTraceAddress hZ history) : ℝ :=
  markedMemoryProjectiveFactor (markedMemoryHistoryTraceAddressPrime hZ history a) q
    (markedMemoryHistoryVertexPositions hZ history) (markedMemoryHistoryVertexPrimitive hZ history)
    (markedMemoryHistoryScalarActiveVisits hZ history a)

theorem markedMemoryHistoryScalarActiveVisits_anchor
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (a : MarkedMemoryHistoryTraceAddress hZ history) (v : Fin (n+1))
    (hv : v ∈ markedMemoryHistoryScalarActiveVisits hZ history a) :
    markedMemoryHistoryTraceAddressAnchor hZ history a =
      ⟨markedMemoryHistoryTraceAddressPrime hZ history a,
        markedMemoryHistoryPrimeLines hZ history (markedMemoryHistoryTraceAddressPrime hZ history a) v⟩ := by
  obtain ⟨band,k,hk⟩ := (Finset.mem_filter.mp hv).2
  have h := markedMemoryHistoryGhostSourceOrigin_anchor hZ history ha v (Sum.inl ⟨band,k⟩)
  rw [hk] at h
  have hp : markedMemoryHistoryTraceAddressPrime hZ history a =
      ((markedMemoryHistoryVertexState hZ history v).2.1 band k).1 :=
    (markedMemoryHistoryTraceAddressAnchor_prime hZ history a).symm.trans (congrArg Sigma.fst h)
  change markedMemoryHistoryTraceAddressAnchor hZ history a =
    ⟨((markedMemoryHistoryVertexState hZ history v).2.1 band k).1,
      markedPrimePositionLine (((markedMemoryHistoryVertexState hZ history v).2.1 band k).1 : ℕ)
        (markedMemoryHistoryVertexState hZ history v).1.1
        (hZ _ (markedMemoryHistoryVertexState hZ history v).1.2)⟩ at h
  rw [← hp] at h
  exact h

theorem markedMemoryHistoryScalarActiveVisits_coherent
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (a : MarkedMemoryHistoryTraceAddress hZ history)
    (hA : (markedMemoryHistoryScalarActiveVisits hZ history a).Nonempty) :
    MarkedMemoryActiveCoherent (markedMemoryHistoryScalarActiveVisits hZ history a)
      (markedMemoryHistoryPrimeLines hZ history (markedMemoryHistoryTraceAddressPrime hZ history a))
      ((markedMemoryHistoryScalarActiveVisits hZ history a).min' hA) := by
  intro v hv
  have h₁ := markedMemoryHistoryScalarActiveVisits_anchor hZ history ha a v hv
  have h₂ := markedMemoryHistoryScalarActiveVisits_anchor hZ history ha a _
    ((markedMemoryHistoryScalarActiveVisits hZ history a).min'_mem hA)
  exact (sigma_mk_injective (β := fun p : Nat.Primes => MarkedRawPrimeLine p)
    (i := markedMemoryHistoryTraceAddressPrime hZ history a)) (h₁.symm.trans h₂)

/-- The exact active indexed factor is the finite sum over optional
birth/death endpoints and its actual internal inactive visit times. -/
theorem markedMemoryHistoryIndexedProjectiveFactor_endpoint_sum
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (a : MarkedMemoryHistoryTraceAddress hZ history)
    (hA : (markedMemoryHistoryScalarActiveVisits hZ history a).Nonempty) (q : ℝ) :
    markedMemoryHistoryIndexedProjectiveFactor hZ history q a =
      (1 / ((markedMemoryHistoryTraceAddressPrime hZ history a : ℝ)+1)) *
        ∑ choice : MarkedMemoryActiveEndpointChoice (markedMemoryHistoryScalarActiveVisits hZ history a) hA,
          markedMemoryActiveEndpointScalar (markedMemoryHistoryScalarActiveVisits hZ history a) hA
            (markedMemoryHistoryScalarVertexAtom hZ history q a) choice := by
  have hc := markedMemoryHistoryScalarActiveVisits_coherent hZ history ha a hA
  have href := markedMemoryHistoryScalarActiveVisits_anchor hZ history ha a _
    ((markedMemoryHistoryScalarActiveVisits hZ history a).min'_mem hA)
  unfold markedMemoryHistoryPrimeLines at hc
  unfold markedMemoryHistoryIndexedProjectiveFactor markedMemoryProjectiveFactor
  rw [markedMemoryPrimeFactor_active _ _ _ _
    ((markedMemoryHistoryScalarActiveVisits hZ history a).min'_mem hA), ite_eq_left hc,
    markedMemoryPrimeLine_card, markedMemoryActiveEndpoint_sum]
  simp only [Nat.cast_add, Nat.cast_one]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  unfold markedMemoryHistoryScalarVertexAtom
  rw [markedMemoryHistoryAddressLineHit_eq_primewise hZ history a _ _ href]
  rfl

/-- Empty indexed active sets retain the singleton baseline, and only
strict birth-before-death pairs enter the orphan correction. -/
theorem markedMemoryHistoryIndexedProjectiveFactor_orphan_sum
    (a : MarkedMemoryHistoryTraceAddress hZ history) (q : ℝ)
    (hA : markedMemoryHistoryScalarActiveVisits hZ history a = ∅) :
    markedMemoryHistoryIndexedProjectiveFactor hZ history q a =
      markedMemoryBaseline q n (markedMemoryHistoryTraceAddressPrime hZ history a) +
        (1 / ((markedMemoryHistoryTraceAddressPrime hZ history a : ℝ)+1)) *
          ∑ choice : MarkedMemoryOrphanEndpointChoice n,
            markedMemoryOrphanEndpointScalar (markedMemoryEta q n)
              (markedMemoryHistoryPrimeLines hZ history (markedMemoryHistoryTraceAddressPrime hZ history a))
              choice := by
  unfold markedMemoryHistoryIndexedProjectiveFactor
  rw [hA, markedMemoryProjectiveFactor_empty, markedMemoryOrphanEndpoint_sum]
  rfl

variable [DecidableEq J]

theorem markedMemoryHistoryIndexedProjectiveFactor_endpoint_sum_of_weight_ne_zero
    (ν : (band : J) → ↥(P band) → ℝ) (V : J → ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (j : ℕ)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0)
    (a : MarkedMemoryHistoryTraceAddress hZ history)
    (hA : (markedMemoryHistoryScalarActiveVisits hZ history a).Nonempty) (q : ℝ) :
    markedMemoryHistoryIndexedProjectiveFactor hZ history q a =
      (1 / ((markedMemoryHistoryTraceAddressPrime hZ history a : ℝ)+1)) *
        ∑ choice : MarkedMemoryActiveEndpointChoice (markedMemoryHistoryScalarActiveVisits hZ history a) hA,
          markedMemoryActiveEndpointScalar (markedMemoryHistoryScalarActiveVisits hZ history a) hA
            (markedMemoryHistoryScalarVertexAtom hZ history q a) choice :=
  markedMemoryHistoryIndexedProjectiveFactor_endpoint_sum hZ history
    (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n j history hw)
    a hA q

end
end ArtinMatthews
