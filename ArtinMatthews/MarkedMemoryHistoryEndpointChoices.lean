module

public import ArtinMatthews.MarkedMemoryHistoryEndpointSums
public import ArtinMatthews.MarkedMemoryHistoryTraceComplete
public import ArtinMatthews.MarkedMemoryHistoryLifespanScalarEvents
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

/-! Actual trace birth/death times give well-typed optional scalar
endpoints. Ghost births precede every active visit; ghost deaths follow
every active visit because active slots survive the intervening ghost. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryHistoryScalarActive_birth_le
    (a : MarkedMemoryHistoryTraceAddress hZ history) (v : Fin (n+1))
    (hv : v ∈ markedMemoryHistoryScalarActiveVisits hZ history a) :
    markedMemoryLineageBirthTime a ≤ 2*v.val := by
  obtain ⟨band,k,hk⟩ := (Finset.mem_filter.mp hv).2
  have h := markedMemoryLineageOrigin_birthTime_le (markedMemoryHistoryTraceStep hZ history)
    (markedMemoryHistoryGhostTime n v) (markedMemoryHistoryGhostSourceIndex hZ history v (Sum.inl ⟨band,k⟩))
  change markedMemoryLineageBirthTime (markedMemoryHistoryGhostSourceOrigin hZ history v (Sum.inl ⟨band,k⟩)) ≤ _ at h
  rw [hk, markedMemoryHistoryGhostTime_eq] at h
  exact h

theorem markedMemoryHistoryScalarActive_survives_ghost
    (a : MarkedMemoryHistoryTraceAddress hZ history) (v : Fin (n+1))
    (hv : v ∈ markedMemoryHistoryScalarActiveVisits hZ history a) :
    2*v.val+1 ≤ markedMemoryHistoryLifespanLast hZ history a := by
  obtain ⟨band,k,hk⟩ := (Finset.mem_filter.mp hv).2
  let target := markedMemoryHistoryGhostTargetIndex hZ history v (Sum.inl ⟨band,k⟩)
  have hs := markedMemoryHistoryGhostStep hZ history v (Sum.inl ⟨band,k⟩)
  rw [markedMemoryGhostPopulationOrigin_active] at hs
  simp only [Sum.map_inl] at hs
  have ho : markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
      (markedMemoryHistoryGhostTime n v+1) target = a := by
    change Sum.elim _ _ (markedMemoryHistoryTraceStep hZ history (markedMemoryHistoryGhostTime n v) target) = a
    rw [hs]
    exact hk
  have ht : markedMemoryHistoryGhostTime n v+1 ≤ 2*n+1 := by
    rw [markedMemoryHistoryGhostTime_eq]
    have hvn := v.isLt
    omega
  have h := (markedMemoryHistory_lifespan_exact hZ history a
    (markedMemoryHistoryGhostTime n v+1)).mp ⟨ht,target,ho⟩
  simpa only [markedMemoryHistoryGhostTime_eq] using h.2

theorem markedMemoryHistoryGhostBirth_before_active
    (t : ℕ) (birth : MarkedMemoryHistoryTraceBirth hZ history t) (ht : t % 2 = 0)
    (v : Fin (n+1))
    (hv : v ∈ markedMemoryHistoryScalarActiveVisits hZ history (Sum.inr ⟨t,birth⟩)) :
    t / 2 < v.val := by
  have h := markedMemoryHistoryScalarActive_birth_le hZ history (Sum.inr ⟨t,birth⟩) v hv
  change t+1 ≤ 2*v.val at h
  omega

theorem markedMemoryHistoryGhostDeath_after_active
    (a : MarkedMemoryHistoryTraceAddress hZ history)
    (ht : markedMemoryHistoryLifespanLast hZ history a % 2 = 0)
    (v : Fin (n+1)) (hv : v ∈ markedMemoryHistoryScalarActiveVisits hZ history a) :
    v.val < markedMemoryHistoryLifespanLast hZ history a / 2 := by
  have h := markedMemoryHistoryScalarActive_survives_ghost hZ history a v hv
  omega

def markedMemoryHistoryActualPrefixChoice
    (a : MarkedMemoryHistoryTraceAddress hZ history)
    (hA : (markedMemoryHistoryScalarActiveVisits hZ history a).Nonempty) :
    MarkedMemoryPrefixChoice ((markedMemoryHistoryScalarActiveVisits hZ history a).min' hA) := by
  cases a with
  | inl old => exact none
  | inr birth =>
    by_cases ht : birth.1 % 2 = 0
    · have hbefore := markedMemoryHistoryGhostBirth_before_active hZ history birth.1 birth.2 ht _
        ((markedMemoryHistoryScalarActiveVisits hZ history (Sum.inr birth)).min'_mem hA)
      exact some ⟨⟨birth.1/2, hbefore.trans
        ((markedMemoryHistoryScalarActiveVisits hZ history (Sum.inr birth)).min' hA).isLt⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbefore⟩⟩
    · exact none

def markedMemoryHistoryActualSuffixChoice
    (a : MarkedMemoryHistoryTraceAddress hZ history)
    (hA : (markedMemoryHistoryScalarActiveVisits hZ history a).Nonempty) :
    MarkedMemorySuffixChoice ((markedMemoryHistoryScalarActiveVisits hZ history a).max' hA) := by
  by_cases ht : markedMemoryHistoryLifespanLast hZ history a % 2 = 0
  · have hafter := markedMemoryHistoryGhostDeath_after_active hZ history a ht _
      ((markedMemoryHistoryScalarActiveVisits hZ history a).max'_mem hA)
    have hbound := (markedMemoryHistory_lifespan_bounds hZ history a).2
    have hfin : markedMemoryHistoryLifespanLast hZ history a / 2 < n+1 := by omega
    exact some ⟨⟨markedMemoryHistoryLifespanLast hZ history a / 2,hfin⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hafter⟩⟩
  · exact none

def markedMemoryHistoryActualEndpointChoice
    (a : MarkedMemoryHistoryTraceAddress hZ history)
    (hA : (markedMemoryHistoryScalarActiveVisits hZ history a).Nonempty) :
    MarkedMemoryActiveEndpointChoice (markedMemoryHistoryScalarActiveVisits hZ history a) hA :=
  (markedMemoryHistoryActualPrefixChoice hZ history a hA, markedMemoryHistoryActualSuffixChoice hZ history a hA)

theorem markedMemoryHistoryActualPrefixChoice_initial
    (old : MarkedMemoryPopulationIndex s)
    (hA : (markedMemoryHistoryScalarActiveVisits hZ history (Sum.inl old)).Nonempty) :
    markedMemoryHistoryActualPrefixChoice hZ history (Sum.inl old) hA = none := rfl

theorem markedMemoryHistoryActualPrefixChoice_ghost_time
    (t : ℕ) (birth : MarkedMemoryHistoryTraceBirth hZ history t) (ht : t % 2 = 0)
    (hA : (markedMemoryHistoryScalarActiveVisits hZ history (Sum.inr ⟨t,birth⟩)).Nonempty) :
    Option.map (fun b => b.1.val)
      (markedMemoryHistoryActualPrefixChoice hZ history (Sum.inr ⟨t,birth⟩) hA) = some (t/2) := by
  simp [markedMemoryHistoryActualPrefixChoice, ht]

theorem markedMemoryHistoryActualPrefixChoice_edge
    (t : ℕ) (birth : MarkedMemoryHistoryTraceBirth hZ history t) (ht : t % 2 ≠ 0)
    (hA : (markedMemoryHistoryScalarActiveVisits hZ history (Sum.inr ⟨t,birth⟩)).Nonempty) :
    markedMemoryHistoryActualPrefixChoice hZ history (Sum.inr ⟨t,birth⟩) hA = none := by
  simp [markedMemoryHistoryActualPrefixChoice, ht]

theorem markedMemoryHistoryActualSuffixChoice_ghost_time
    (a : MarkedMemoryHistoryTraceAddress hZ history)
    (hA : (markedMemoryHistoryScalarActiveVisits hZ history a).Nonempty)
    (ht : markedMemoryHistoryLifespanLast hZ history a % 2 = 0) :
    Option.map (fun d => d.1.val) (markedMemoryHistoryActualSuffixChoice hZ history a hA) =
      some (markedMemoryHistoryLifespanLast hZ history a / 2) := by
  simp [markedMemoryHistoryActualSuffixChoice, ht]

theorem markedMemoryHistoryActualSuffixChoice_edge_or_terminal
    (a : MarkedMemoryHistoryTraceAddress hZ history)
    (hA : (markedMemoryHistoryScalarActiveVisits hZ history a).Nonempty)
    (ht : markedMemoryHistoryLifespanLast hZ history a % 2 ≠ 0) :
    markedMemoryHistoryActualSuffixChoice hZ history a hA = none := by
  simp [markedMemoryHistoryActualSuffixChoice, ht]

/-- A ghost-born identity with a ghost death gives a strict finite
birth/death interval. This also supplies the coordinates for an orphan. -/
def markedMemoryHistoryGhostIntervalChoice
    (t : ℕ) (birth : MarkedMemoryHistoryTraceBirth hZ history t) (ht : t % 2 = 0)
    (hd : markedMemoryHistoryLifespanLast hZ history (Sum.inr ⟨t,birth⟩) % 2 = 0) :
    MarkedMemoryOrphanEndpointChoice n := by
  have hb := markedMemoryHistoryTraceBirth_time_lt hZ history t birth
  have hl := markedMemoryHistory_lifespan_bounds hZ history (Sum.inr ⟨t,birth⟩)
  change t+1 ≤ _ ∧ _ at hl
  have hfirst : t/2 < n+1 := by omega
  have hlast : markedMemoryHistoryLifespanLast hZ history (Sum.inr ⟨t,birth⟩)/2 < n+1 := by omega
  have horder : t/2 < markedMemoryHistoryLifespanLast hZ history (Sum.inr ⟨t,birth⟩)/2 := by omega
  exact ⟨⟨t/2,hfirst⟩, ⟨⟨markedMemoryHistoryLifespanLast hZ history (Sum.inr ⟨t,birth⟩)/2,hlast⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, horder⟩⟩⟩

theorem markedMemoryHistoryGhostIntervalChoice_first
    (t : ℕ) (birth : MarkedMemoryHistoryTraceBirth hZ history t) (ht : t % 2 = 0)
    (hd : markedMemoryHistoryLifespanLast hZ history (Sum.inr ⟨t,birth⟩) % 2 = 0) :
    (markedMemoryHistoryGhostIntervalChoice hZ history t birth ht hd).1.val = t/2 := rfl

theorem markedMemoryHistoryGhostIntervalChoice_last
    (t : ℕ) (birth : MarkedMemoryHistoryTraceBirth hZ history t) (ht : t % 2 = 0)
    (hd : markedMemoryHistoryLifespanLast hZ history (Sum.inr ⟨t,birth⟩) % 2 = 0) :
    (markedMemoryHistoryGhostIntervalChoice hZ history t birth ht hd).2.1.val =
      markedMemoryHistoryLifespanLast hZ history (Sum.inr ⟨t,birth⟩)/2 := rfl

end
end ArtinMatthews
