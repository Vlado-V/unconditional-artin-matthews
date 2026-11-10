module

public import ArtinMatthews.MarkedMinorArcRawEdgeChargedAction
public import ArtinMatthews.MarkedMinorArcRawEdgeTotalTranspose
public import ArtinMatthews.MarkedMinorArcRawEdgeMemoryNormalForm
public import ArtinMatthews.MarkedMinorArcRawEdgePairingFibers
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted transpose of the full literal coupled store/promote action.
The source and target cutoffs, old-index multiplicities and all endpoint
restrictions remain in the actual indexed state space. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedRawEdgePositionPairing
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (copied : MarkedRawActive P pads) (x y : Z)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ) : ℂ :=
  ∑ t : MarkedRawEdgeDegrees J B,
    markedRawEdgeDegreePairing P (fun j p => (ν j p : ℂ)) hZ x y copied t δ γ K

theorem markedRawEdge_position_pairing_transpose
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (copied : MarkedRawActive P pads) (x y : Z)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ)
    (hKleft : ∀ z active target, MarkedRawMemorySymmetric (fun m => K (z,(active,m)) target))
    (hKright : ∀ source z active, MarkedRawMemorySymmetric (fun m => K source (z,(active,m)))) :
    markedRawEdgePositionPairing ν δ γ hZ copied x y K =
      markedRawEdgePositionPairing ν γ δ hZ copied y x (fun target source => K source target) :=
  markedRawEdge_total_degree_transpose P (fun j p => (ν j p : ℂ))
    hZ x y copied δ γ K hKleft hKright

attribute [local irreducible] markedRawEdgePositionPairing

def markedRawEdgeFullDegreePairing
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ) : ℂ :=
  ∑ copied : MarkedRawActive P pads, (markedRawActiveMass ν copied : ℂ) *
    ∑ x : Z, ∑ y : Z, markedRawEdgePositionPairing ν δ γ hZ copied x y K

theorem markedRawEdge_full_degree_normalForm
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ s, (markedRawStateMass ν s : ℂ) *
      markedRawEdgeChargedApply ν δ γ hZ K (fun _ => 1) s) =
      markedRawEdgeFullDegreePairing ν δ γ hZ K := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  rw [markedRawState_sum_last_fibers]
  unfold markedRawEdgeFullDegreePairing
  apply Finset.sum_congr rfl
  intro copied _
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  unfold markedRawEdgePositionPairing
  exact markedRawEdge_charged_memory_normalForm ν δ γ hZ x copied K

theorem markedRawEdge_full_degree_transpose
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ)
    (hKleft : ∀ z active target, MarkedRawMemorySymmetric (fun m => K (z,(active,m)) target))
    (hKright : ∀ source z active, MarkedRawMemorySymmetric (fun m => K source (z,(active,m)))) :
    markedRawEdgeFullDegreePairing ν δ γ hZ K =
      markedRawEdgeFullDegreePairing ν γ δ hZ (fun target source => K source target) := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  unfold markedRawEdgeFullDegreePairing
  apply Finset.sum_congr rfl
  intro copied _
  congr 1
  calc
    _ = ∑ x : Z, ∑ y : Z,
        markedRawEdgePositionPairing ν γ δ hZ copied y x (fun target source => K source target) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact markedRawEdge_position_pairing_transpose ν δ γ hZ copied x y K hKleft hKright
    _ = _ := Finset.sum_comm

theorem markedRawEdge_full_pairing_transpose
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ)
    (hKleft : ∀ z active target, MarkedRawMemorySymmetric (fun m => K (z,(active,m)) target))
    (hKright : ∀ source z active, MarkedRawMemorySymmetric (fun m => K source (z,(active,m)))) :
    (∑ s, (markedRawStateMass ν s : ℂ) *
      markedRawEdgeChargedApply ν δ γ hZ K (fun _ => 1) s) =
      ∑ s, (markedRawStateMass ν s : ℂ) *
        markedRawEdgeChargedApply ν γ δ hZ (fun target source => K source target) (fun _ => 1) s := by
  rw [markedRawEdge_full_degree_normalForm, markedRawEdge_full_degree_normalForm]
  exact markedRawEdge_full_degree_transpose ν δ γ hZ K hKleft hKright

/-- The actual charged row and its swapped-charge reverse obey the true
state-mass bilinear transpose on pending-symmetric observables. -/
theorem markedRawEdgeChargedApply_transpose
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ)
    (hKleft : ∀ z active target, MarkedRawMemorySymmetric (fun m => K (z,(active,m)) target))
    (hKright : ∀ source z active, MarkedRawMemorySymmetric (fun m => K source (z,(active,m))))
    (f g : MarkedRawState P (pads+1) B Z → ℂ)
    (hf : ∀ z active, MarkedRawMemorySymmetric (fun m => f (z,(active,m))))
    (hg : ∀ z active, MarkedRawMemorySymmetric (fun m => g (z,(active,m)))) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s * markedRawEdgeChargedApply ν δ γ hZ K f s) =
      ∑ s, (markedRawStateMass ν s : ℂ) * f s *
        markedRawEdgeChargedApply ν γ δ hZ (fun target source => K source target) g s := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  let L := fun s t => g s * K s t * f t
  have hleft : ∀ z active target, MarkedRawMemorySymmetric (fun m => L (z,(active,m)) target) := by
    intro z active target m σ
    have h1 : g (z,(active,markedRawMemoryPermute m σ)) = g (z,(active,m)) := hg z active m σ
    have h2 : K (z,(active,markedRawMemoryPermute m σ)) target = K (z,(active,m)) target :=
      hKleft z active target m σ
    dsimp only [L]
    rw [h1,h2]
  have hright : ∀ source z active, MarkedRawMemorySymmetric (fun m => L source (z,(active,m))) := by
    intro source z active m σ
    have h1 : f (z,(active,markedRawMemoryPermute m σ)) = f (z,(active,m)) := hf z active m σ
    have h2 : K source (z,(active,markedRawMemoryPermute m σ)) = K source (z,(active,m)) :=
      hKright source z active m σ
    dsimp only [L]
    rw [h1,h2]
  have h := markedRawEdge_full_pairing_transpose ν δ γ hZ L hleft hright
  simpa only [markedRawEdgeChargedApply, L, mul_one, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using h

end
end ArtinMatthews
