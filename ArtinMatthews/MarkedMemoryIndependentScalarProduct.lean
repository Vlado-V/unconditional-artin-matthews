module

public import ArtinMatthews.MarkedMemoryIndependentCorrespondence
public import ArtinMatthews.MarkedMemoryIndependentScalarEvents
public import ArtinMatthews.MarkedMemoryIndependentScalarLabels
public import ArtinMatthews.MarkedMemoryScalarFibers
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

/-! Explicit scalar factors of the independent lifespan tableau. Each
vertex contributes the actual old-pending scalar and the ghost-birth
scalar, using the first/last/active incidence and original visit time. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  {A : J → Type*} [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "history" => markedMemoryIndependentHistory hZ d order
local notation "addr" => markedMemoryIndependentAddressEquiv hZ d order

def markedMemoryIndependentOldScalar (qStage : ℕ → ℝ) (offset : ℕ)
    (v : Fin (n+1)) (a : Σ j, A j) : ℝ :=
  if (d.lifespan a.1).last a.2 = 2*v.val then -(1-qStage (offset+v.val))
  else if MarkedRawParticleHits (P a.1) (d.position v.val).1
    (hZ _ (d.position v.val).2) (d.particle a.1 a.2) then qStage (offset+v.val) else 1

def markedMemoryIndependentLifespanScalar (qStage : ℕ → ℝ) (offset : ℕ) (a : Σ j, A j) : ℝ :=
  ∏ v : Fin (n+1),
    (if a.2 ∈ markedMemoryIndependentQueue hZ d (2*v.val) a.1
      then markedMemoryIndependentOldScalar hZ d qStage offset v a else 1) *
    (if a.2 ∈ (d.lifespan a.1).births (2*v.val) then -(1-qStage (offset+v.val)) else 1)

theorem markedMemoryIndependentScalar_vertex (qStage : ℕ → ℝ) (offset : ℕ)
    (v : Fin (n+1)) (a : Σ j, A j) :
    (∏ event : MarkedMemoryIndependentGhostEventAt hZ d v,
      if markedMemoryIndependentGhostEventLabel hZ d ⟨v,event⟩ = a
      then markedMemoryIndependentGhostEventValue hZ d qStage offset ⟨v,event⟩ else 1) =
    (if a.2 ∈ markedMemoryIndependentQueue hZ d (2*v.val) a.1
      then markedMemoryIndependentOldScalar hZ d qStage offset v a else 1) *
    (if a.2 ∈ (d.lifespan a.1).births (2*v.val) then -(1-qStage (offset+v.val)) else 1) := by
  rw [Fintype.prod_sum_type]
  apply congrArg₂ (fun x y : ℝ => x*y)
  · apply markedMemoryListFamily_scalar (markedMemoryIndependentQueue hZ d (2*v.val))
      (fun j => markedMemoryPendingQueueAt_nodup (d.lifespan j) (2*v.val) (by omega)) a
    rintro ⟨j,k⟩ he
    rcases a with ⟨i,a⟩
    change (⟨j,(markedMemoryIndependentQueue hZ d (2*v.val) j).get k⟩ : Σ j, A j) = ⟨i,a⟩ at he
    obtain ⟨rfl,ha⟩ := Sigma.mk.inj_iff.mp he
    have ha' : (markedMemoryIndependentQueue hZ d (2*v.val) j).get k = a := eq_of_heq ha
    subst a
    rfl
  · apply markedMemoryListFamily_scalar (fun j => (d.lifespan j).births (2*v.val))
      (fun j => (d.lifespan j).ghost_nodup (2*v.val) (by omega) (by omega)) a
    intro x _
    rfl

def markedMemoryIndependentScalarFiberEquiv (a : Σ j, A j) :
    {event : MarkedMemoryHistoryGhostScalarEvent hZ history //
      markedMemoryHistoryGhostScalarOrigin hZ history event = (addr).symm a} ≃
    {event : MarkedMemoryIndependentGhostEvent hZ d //
      markedMemoryIndependentGhostEventLabel hZ d event = a} :=
  (markedMemoryIndependentScalarEventsEquiv hZ d order).subtypeEquiv (fun event => by
    have he := markedMemoryIndependentScalarEvents_label hZ d order event
    constructor
    · intro ha
      exact he.symm.trans ((congrArg addr ha).trans ((addr).apply_symm_apply a))
    · intro ha
      apply (addr).injective
      exact he.trans (ha.trans ((addr).apply_symm_apply a).symm))

theorem markedMemoryIndependent_lifespanScalar (qStage : ℕ → ℝ) (offset : ℕ) (a : Σ j, A j) :
    markedMemoryHistoryLifespanScalar hZ history qStage offset ((addr).symm a) =
      markedMemoryIndependentLifespanScalar hZ d qStage offset a := by
  unfold markedMemoryHistoryLifespanScalar
  rw [← Equiv.prod_comp (markedMemoryIndependentScalarFiberEquiv hZ d order a).symm]
  calc
    _ = ∏ event : {event : MarkedMemoryIndependentGhostEvent hZ d //
        markedMemoryIndependentGhostEventLabel hZ d event = a},
        markedMemoryIndependentGhostEventValue hZ d qStage offset event.1 := by
      apply Finset.prod_congr rfl
      intro event _
      have hv := markedMemoryIndependentScalarEvents_value hZ d order qStage offset
        ((markedMemoryIndependentScalarFiberEquiv hZ d order a).symm event).1
      have he := congrArg Subtype.val ((markedMemoryIndependentScalarFiberEquiv hZ d order a).apply_symm_apply event)
      exact hv.trans (congrArg (markedMemoryIndependentGhostEventValue hZ d qStage offset) he)
    _ = ∏ event : MarkedMemoryIndependentGhostEvent hZ d,
        if markedMemoryIndependentGhostEventLabel hZ d event = a
        then markedMemoryIndependentGhostEventValue hZ d qStage offset event else 1 :=
      markedMemoryScalarFiber_ite _ a _
    _ = _ := by
      rw [Fintype.prod_sigma]
      exact Finset.prod_congr rfl (fun v _ => markedMemoryIndependentScalar_vertex hZ d qStage offset v a)

omit [DecidableEq J] in
theorem markedMemoryIndependentLifespanScalar_endpoints (qStage : ℕ → ℝ) (offset : ℕ)
    (a : Σ j, A j) :
    markedMemoryIndependentLifespanScalar hZ d qStage offset a =
      ∏ v : Fin (n+1),
        (if (d.lifespan a.1).first a.2 ≤ 2*v.val ∧ 2*v.val ≤ (d.lifespan a.1).last a.2 ∧
            ¬ (d.lifespan a.1).active (2*v.val) a.2
          then markedMemoryIndependentOldScalar hZ d qStage offset v a else 1) *
        (if (d.lifespan a.1).first a.2 = 2*v.val+1 ∧ 2*v.val+1 ≤ (d.lifespan a.1).last a.2 ∧
            ¬ (d.lifespan a.1).active (2*v.val) a.2
          then -(1-qStage (offset+v.val)) else 1) := by
  unfold markedMemoryIndependentLifespanScalar
  apply Finset.prod_congr rfl
  intro v _
  simp only [markedMemoryIndependentQueue,
    markedMemoryPendingQueueAt_mem (d.lifespan a.1) (2*v.val) (by omega),
    (d.lifespan a.1).ghost_births (2*v.val) (by omega) (by omega)]

end
end ArtinMatthews
