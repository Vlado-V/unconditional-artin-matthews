module

public import ArtinMatthews.MarkedInjectedBirthMass
public import ArtinMatthews.MarkedMemoryBirthStagePivots
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

/-! Actual stage-wise birth addresses and conditional prime masses.
Initial slots, every ordered ghost batch and each fresh edge label use
the same proved earlier-pivot integration, with absent slots kept none. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryInitialDraw {J : Type*} {M B N : ℕ}
    (a : Σ _j : J, Fin M) : MarkedMemoryPotentialAddress J M B N := Sum.inl (a.1,a.2)

theorem markedMemoryInitialDraw_injective {J : Type*} {M B N : ℕ} :
    Function.Injective (markedMemoryInitialDraw (J := J) (M := M) (B := B) (N := N)) := by
  intro a b h
  rcases a with ⟨j,k⟩
  rcases b with ⟨i,l⟩
  have hp := Sum.inl.inj h
  have hj : j=i := congrArg Prod.fst hp
  subst i
  have hk : k=l := congrArg Prod.snd hp
  subst l
  rfl

def markedMemoryGhostStageDraw {J : Type*} {M B N : ℕ}
    (t : Fin (N+1)) (l : J → Fin (B+1))
    (a : Σ j, Fin (l j : ℕ)) : MarkedMemoryPotentialAddress J M B N :=
  Sum.inr (Sum.inl ⟨t,a.1,⟨a.2.1,a.2.2.trans_le (Nat.le_of_lt_succ (l a.1).2)⟩⟩)

theorem markedMemoryGhostStageDraw_injective {J : Type*} {M B N : ℕ}
    (t : Fin (N+1)) (l : J → Fin (B+1)) :
    Function.Injective (markedMemoryGhostStageDraw (M := M) t l) := by
  intro a b h
  rcases a with ⟨j,k⟩
  rcases b with ⟨i,hk⟩
  have he := congrArg Prod.snd (Sum.inl.inj (Sum.inr.inj h))
  have hj : j=i := congrArg Prod.fst he
  subst i
  have hi : k=hk := Fin.ext (congrArg (fun p => p.2.1) he)
  subst hk
  rfl

def markedMemoryEdgeStageDraw {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (t : Fin N) (I : Finset J) (j : ↥(Finset.univ \ I)) :
    MarkedMemoryPotentialAddress J M B N := Sum.inr (Sum.inr ⟨t,j.1⟩)

theorem markedMemoryEdgeStageDraw_injective {J : Type*} [Fintype J] [DecidableEq J]
    {M B N : ℕ} (t : Fin N) (I : Finset J) :
    Function.Injective (markedMemoryEdgeStageDraw (M := M) (B := B) t I) := by
  intro a b h
  exact Subtype.ext (congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj h)))

def markedMemoryStageBase {J : Type*} {M B N : ℕ} (stage : ℕ)
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (a : MarkedMemoryPotentialAddress J M B N) : Option Nat.Primes :=
  if markedMemoryPotentialChronologicalTime a=stage then none else old a

def markedMemoryStageBirthGate {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    {P : J → Finset Nat.Primes} {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (stage : ℕ)
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (e : I → MarkedMemoryPotentialAddress J M B N) (he : Function.Injective e)
    (t : (i : I) → ↥(P (markedMemoryPotentialGroup (e i)))) : Prop :=
  MarkedConditionalBirthGate (P := fun a => P (markedMemoryPotentialGroup a))
    (markedMemoryStageNonpivots σ stage) (markedMemoryPotentialPivot σ)
    (markedMemoryStageBase stage old) (markedBirthDrawSet e)
    (markedBirthDrawTupleEquiv (fun a => P (markedMemoryPotentialGroup a)) e he t)

def markedMemoryStageBirthValues {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    {P : J → Finset Nat.Primes} {M B N : ℕ}
    (stage : ℕ) (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (e : I → MarkedMemoryPotentialAddress J M B N) (he : Function.Injective e)
    (t : (i : I) → ↥(P (markedMemoryPotentialGroup (e i)))) :
    MarkedMemoryPotentialAddress J M B N → Option Nat.Primes :=
  markedConditionalBirthValues (P := fun a => P (markedMemoryPotentialGroup a))
    (markedMemoryStageBase stage old) (markedBirthDrawSet e)
    (markedBirthDrawTupleEquiv (fun a => P (markedMemoryPotentialGroup a)) e he t)

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryStageBirth_mass_le
    {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) {Δ D : ℝ} (hΔ : 0 ≤ Δ) (hD : 1 ≤ D)
    (hatom : ∀ j p,ν j p ≤ Δ) (hmass : ∀ j,(∑ p : P j,ν j p) ≤ D)
    {M B N : ℕ} (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (stage : ℕ)
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (e : I → MarkedMemoryPotentialAddress J M B N) (he : Function.Injective e) :
    (∑ t : (i : I) → ↥(P (markedMemoryPotentialGroup (e i))),
      if markedMemoryStageBirthGate σ stage old e he t then
        ∏ i,ν (markedMemoryPotentialGroup (e i)) (t i) else 0) ≤
      Δ^(markedMemoryStageNonpivots σ stage).card*D^(Fintype.card I) := by
  let _ : LinearOrder (MarkedMemoryPotentialAddress J M B N) := markedMemoryPotentialChronologicalOrder
  unfold markedMemoryStageBirthGate
  apply markedInjectedBirth_sum_le (P := fun a => P (markedMemoryPotentialGroup a))
    (fun a => ν (markedMemoryPotentialGroup a))
    (fun a => hν (markedMemoryPotentialGroup a)) hΔ hD
    (fun a => hatom (markedMemoryPotentialGroup a)) (fun a => hmass (markedMemoryPotentialGroup a))
    e he (markedMemoryStageNonpivots σ stage) (markedMemoryPotentialPivot σ)
    (markedMemoryStageBase stage old)
  · intro a ha
    exact markedMemoryStageNonpivots_parent_earlier σ stage ha
  · intro a ha _
    exact ite_eq_left (Finset.mem_filter.mp ha).2

end ArtinMatthews
