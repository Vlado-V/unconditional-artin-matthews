module

public import ArtinMatthews.MarkedMemoryActualPhysicalLabels
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

/-! Empty initial pending memory fixes each static address anchor at
its birth vertex. Ghost births use their source vertex; fresh edge
births use their target vertex. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)

theorem markedMemoryHistoryTraceBirthAnchor_birthPosition
    {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (b : MarkedMemoryHistoryTraceBirth hZ history t) :
    markedMemoryHistoryTraceBirthAnchor hZ history t b =
      ⟨markedMemoryHistoryTraceBirthPrime hZ history t b,
        markedPrimePositionLine (markedMemoryHistoryTraceBirthPrime hZ history t b : ℕ)
          (markedMemoryHistoryTraceState hZ history (2*((t+1)/2))).1.1
          (hZ _ (markedMemoryHistoryTraceState hZ history (2*((t+1)/2))).1.2)⟩ := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => rfl
    | succ t => exact PEmpty.elim b
  | succ n ih =>
    cases t with
    | zero => rfl
    | succ t =>
      cases t with
      | zero => rfl
      | succ t =>
        have ht : 2*((t+2+1)/2)=2*((t+1)/2)+2 := by omega
        simpa only [markedMemoryHistoryTraceBirthAnchor,markedMemoryHistoryTraceBirthPrime,ht,
          markedMemoryHistoryTraceState,markedMemoryHistoryTraceStateAux] using ih history.2.2 t b

theorem markedMemoryHistoryTraceAddressAnchor_birthPosition
    {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (a : MarkedMemoryHistoryTraceAddress hZ history) :
    markedMemoryHistoryTraceAddressAnchor hZ history a =
      ⟨markedMemoryHistoryTraceAddressPrime hZ history a,
        markedPrimePositionLine (markedMemoryHistoryTraceAddressPrime hZ history a : ℕ)
          (markedMemoryActualPosition hZ history (markedMemoryLineageBirthTime a/2)).1
          (hZ _ (markedMemoryActualPosition hZ history (markedMemoryLineageBirthTime a/2)).2)⟩ := by
  cases a with
  | inl old =>
    cases old with
    | inl old =>
      rcases old with ⟨j,k⟩
      simp only [markedMemoryHistoryTraceAddressAnchor,markedMemoryHistoryTraceAddressPrime,
        markedMemoryPopulationAnchor,markedMemoryPopulationPrime,Sum.elim_inl,
        markedMemoryLineageBirthTime,Nat.zero_div,Nat.mul_zero,markedMemoryActualPosition,
        markedMemoryHistoryTraceState,markedMemoryHistoryTraceStateAux]
    | inr old =>
      rcases old with ⟨j,k⟩
      have hk := k.isLt
      have hs : markedMemoryHistoryTraceState hZ history 0 = s := by cases n <;> rfl
      have hc : ((markedMemoryHistoryTraceState hZ history 0).2.2.1.1 j:ℕ)=0 :=
        (congrArg (fun z : MarkedRawState P (pads+1) B Z => (z.2.2.1.1 j:ℕ)) hs).trans (hempty j)
      omega
  | inr birth =>
    rcases birth with ⟨t,b⟩
    exact markedMemoryHistoryTraceBirthAnchor_birthPosition hZ history t b

theorem markedMemoryActualParticle_birthPosition
    {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (j : J) (a : MarkedMemoryActualFiber hZ history j) :
    markedMemoryActualParticle hZ history j a =
      markedRawAnchoredParticle (P j) (markedMemoryActualParticle hZ history j a).1
        (markedMemoryActualPosition hZ history (markedMemoryActualFirst hZ history j a/2)).1
        (hZ _ (markedMemoryActualPosition hZ history (markedMemoryActualFirst hZ history j a/2)).2) := by
  apply markedMemoryForgetBandParticle_injective
  rw [markedMemoryActualParticle_forget]
  change _ =
    (⟨(markedMemoryActualParticle hZ history j a).1.1,
      markedPrimePositionLine ((markedMemoryActualParticle hZ history j a).1.1:ℕ)
        (markedMemoryActualPosition hZ history (markedMemoryActualFirst hZ history j a/2)).1
        (hZ _ (markedMemoryActualPosition hZ history (markedMemoryActualFirst hZ history j a/2)).2)⟩ :
      MarkedMemoryAnchoredPrime)
  rw [markedMemoryActualParticle_prime]
  exact markedMemoryHistoryTraceAddressAnchor_birthPosition hZ history hempty a.1

end
end ArtinMatthews
