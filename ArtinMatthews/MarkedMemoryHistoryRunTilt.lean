module

public import ArtinMatthews.MarkedMemoryHistoryRunWeight
public import ArtinMatthews.MarkedMemoryHistoryRunPowers
public import ArtinMatthews.MarkedMemoryTiltBasic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual grouped nu/V factor of each performed birth has exactly
the original inverse-V charge for every active run, together with one
uniform projective-line factor and one baseline denominator. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (V : J → ℝ) (hV : ∀ j, V j ≠ 0) (q : ℝ) (N : ℕ)
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

include hV

/-- A ghost-born identity contributes V nu and no initial active-run
charge; a fresh edge birth contributes nu and its initial active-run
charge. Every subsequent actual promotion contributes one more inverse V. -/
theorem markedMemoryHistory_birth_run_charge (t : ℕ)
    (b : MarkedMemoryHistoryTraceBirth hZ history t) :
    let a : MarkedMemoryHistoryTraceAddress hZ history := Sum.inr ⟨t,b⟩
    let i := markedMemoryHistoryTraceBirthEquiv hZ history ⟨t,b⟩
    let p := markedMemoryHistoryBirthLabel hZ history i
    markedMemoryHistoryTraceBirthMass
        (fun j p => markedMemoryPrimeAtom (V j) q N (p.1 : ℕ)) V hZ history a *
      markedMemoryHistoryRunMass V hZ history a =
      (V p.1)⁻¹ ^ (if markedMemoryHistoryBirthIsGhost hZ history i then
          markedMemoryHistoryRunCount hZ history a else markedMemoryHistoryRunCount hZ history a+1) *
        (1 / ((((p.2.1 : ℕ) : ℝ)+1)*markedMemoryBaseline q N (p.2.1 : ℕ))) := by
  dsimp only
  rw [markedMemoryHistoryRunMass_pow]
  let i := markedMemoryHistoryTraceBirthEquiv hZ history ⟨t,b⟩
  let p := markedMemoryHistoryBirthLabel hZ history i
  let r := markedMemoryHistoryRunCount hZ history (Sum.inr ⟨t,b⟩)
  change ((if markedMemoryHistoryBirthIsGhost hZ history i then V p.1 else 1) *
      markedMemoryPrimeAtom (V p.1) q N (p.2.1 : ℕ)) * (V p.1)⁻¹ ^ r =
    (V p.1)⁻¹ ^ (if markedMemoryHistoryBirthIsGhost hZ history i then r else r+1) *
      (1 / ((((p.2.1 : ℕ) : ℝ)+1)*markedMemoryBaseline q N (p.2.1 : ℕ)))
  cases hg : markedMemoryHistoryBirthIsGhost hZ history i with
  | false =>
    simpa only [hg, Bool.false_eq_true, ite_false, one_mul] using
      markedMemory_active_run_charge (V p.1) q N (p.2.1 : ℕ) r
  | true =>
    simpa only [hg, Bool.true_eq, ite_true] using
      markedMemory_ghost_run_charge (hV p.1) q N (p.2.1 : ℕ) r

end
end ArtinMatthews
