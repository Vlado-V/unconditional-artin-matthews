module

public import ArtinMatthews.MarkedMemoryStageBirthMass
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

/-! Initial active slots are genuine independent tilted-prime draws.
The initial portion of the chronological pivot event costs one atom for
each of its selected nonpivots, with every ordered slot retained. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryInitialPivotGate
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (active : MarkedRawActive P M) : Prop :=
  markedMemoryStageBirthGate σ 0 old markedMemoryInitialDraw markedMemoryInitialDraw_injective
    (fun a => active a.1 a.2)

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryInitialPivot_mass_le
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p,0 ≤ ν j p)
    {Δ D : ℝ} (hΔ : 0 ≤ Δ) (hD : 1 ≤ D)
    (hatom : ∀ j p,ν j p ≤ Δ) (hmass : ∀ j,(∑ p : P j,ν j p) ≤ D)
    {M B N : ℕ} (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes) :
    (∑ active : MarkedRawActive P M,
      if markedMemoryInitialPivotGate σ old active then markedRawActiveMass ν active else 0) ≤
      Δ^(markedMemoryStageNonpivots σ 0).card*D^(Fintype.card J*M) := by
  have h := markedMemoryStageBirth_mass_le ν hν hΔ hD hatom hmass σ 0 old
    markedMemoryInitialDraw markedMemoryInitialDraw_injective
  let E := Equiv.piCurry (fun j (_k : Fin M) => ↥(P j))
  have heq := E.sum_comp (fun active =>
    if markedMemoryInitialPivotGate σ old active then markedRawActiveMass ν active else 0)
  have heq' : (∑ active : MarkedRawActive P M,
      if markedMemoryInitialPivotGate σ old active then markedRawActiveMass ν active else 0) =
      ∑ u : (a : Σ _j : J,Fin M) → ↥(P a.1),
        if markedMemoryStageBirthGate σ 0 old markedMemoryInitialDraw markedMemoryInitialDraw_injective u
        then ∏ a,ν a.1 (u a) else 0 := by
    simpa only [E,Equiv.piCurry_apply,Sigma.curry,Sigma.eta,markedMemoryInitialPivotGate,markedRawActiveMass,Fintype.prod_sigma] using heq.symm
  rw [heq']
  refine le_trans (le_of_eq ?_) (h.trans_eq ?_)
  · apply Finset.sum_congr (by ext; simp only [Finset.mem_univ])
    intro u _
    rfl
  · simp [Fintype.card_sigma]

end ArtinMatthews
