module

public import ArtinMatthews.MarkedMinorArcRawEdgePatternNormalForm
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

/-! Exact full-state transpose for literal flag-dependent edge kernels.
Promoted and stored flags exchange, together with their charges and the
ordered endpoint arguments.  Both total-memory caps remain present. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawEdge_pattern_position_transpose
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (copied : MarkedRawActive P pads) (x y : Z)
    (A : MarkedRawEdgePatternKernel P pads B Z)
    (hAl : ∀ p q z active target, MarkedRawMemorySymmetric (fun m => A p q (z,(active,m)) target))
    (hAr : ∀ p q source z active, MarkedRawMemorySymmetric (fun m => A p q source (z,(active,m)))) :
    markedRawEdgePatternPositionPairing ν δ γ hZ copied x y A =
      markedRawEdgePatternPositionPairing ν γ δ hZ copied y x (markedRawEdgePatternReverse A) := by
  classical
  unfold markedRawEdgePatternPositionPairing
  calc
    _ = ∑ t : MarkedRawEdgeDegrees J B,
        markedRawEdgeDegreePairing P (fun j p => (ν j p : ℂ)) hZ y x copied
          (markedRawEdgeDegreesSwap t) γ δ
          ((markedRawEdgePatternReverse A) (markedRawEdgeDegreesSwap t).promoted
            (markedRawEdgeDegreesSwap t).stored) := by
      apply Finset.sum_congr rfl
      intro t _
      exact markedRawEdge_degree_pairing_transpose P (fun j p => (ν j p : ℂ))
        hZ x y copied t δ γ (A t.promoted t.stored) (hAl _ _) (hAr _ _)
    _ = _ := (markedRawEdgeDegreesSwap (J := J) (B := B)).sum_comp
      (fun t => markedRawEdgeDegreePairing P (fun j p => (ν j p : ℂ)) hZ y x copied t γ δ
        ((markedRawEdgePatternReverse A) t.promoted t.stored))

attribute [local irreducible] markedRawEdgePatternPositionPairing

def markedRawEdgePatternFullPairing
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z) : ℂ :=
  ∑ copied : MarkedRawActive P pads, (markedRawActiveMass ν copied : ℂ) *
    ∑ x : Z, ∑ y : Z, markedRawEdgePatternPositionPairing ν δ γ hZ copied x y A

theorem markedRawEdge_pattern_full_normalForm
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z) :
    (∑ s, (markedRawStateMass ν s : ℂ) *
      markedRawEdgePatternApply ν δ γ hZ A (fun _ => 1) s) =
      markedRawEdgePatternFullPairing ν δ γ hZ A := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  rw [markedRawState_sum_last_fibers]
  unfold markedRawEdgePatternFullPairing
  apply Finset.sum_congr rfl
  intro copied _
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact markedRawEdge_pattern_memory_normalForm ν δ γ hZ x copied A

theorem markedRawEdge_pattern_full_pairing_transpose
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (hAl : ∀ p q z active target, MarkedRawMemorySymmetric (fun m => A p q (z,(active,m)) target))
    (hAr : ∀ p q source z active, MarkedRawMemorySymmetric (fun m => A p q source (z,(active,m)))) :
    markedRawEdgePatternFullPairing ν δ γ hZ A =
      markedRawEdgePatternFullPairing ν γ δ hZ (markedRawEdgePatternReverse A) := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  unfold markedRawEdgePatternFullPairing
  apply Finset.sum_congr rfl
  intro copied _
  congr 1
  calc
    _ = ∑ x : Z, ∑ y : Z,
        markedRawEdgePatternPositionPairing ν γ δ hZ copied y x (markedRawEdgePatternReverse A) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact markedRawEdge_pattern_position_transpose ν δ γ hZ copied x y A hAl hAr
    _ = _ := Finset.sum_comm

theorem markedRawEdgePatternApply_transpose
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (hAl : ∀ p q z active target, MarkedRawMemorySymmetric (fun m => A p q (z,(active,m)) target))
    (hAr : ∀ p q source z active, MarkedRawMemorySymmetric (fun m => A p q source (z,(active,m))))
    (f g : MarkedRawState P (pads+1) B Z → ℂ)
    (hf : ∀ z active, MarkedRawMemorySymmetric (fun m => f (z,(active,m))))
    (hg : ∀ z active, MarkedRawMemorySymmetric (fun m => g (z,(active,m)))) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s * markedRawEdgePatternApply ν δ γ hZ A f s) =
      ∑ s, (markedRawStateMass ν s : ℂ) * f s *
        markedRawEdgePatternApply ν γ δ hZ (markedRawEdgePatternReverse A) g s := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  let L : MarkedRawEdgePatternKernel P pads B Z := fun p q s t => g s * A p q s t * f t
  have hLl : ∀ p q z active target, MarkedRawMemorySymmetric (fun m => L p q (z,(active,m)) target) := by
    intro p q z active target m σ
    have h1 : g (z,(active,markedRawMemoryPermute m σ)) = g (z,(active,m)) := hg z active m σ
    have h2 : A p q (z,(active,markedRawMemoryPermute m σ)) target = A p q (z,(active,m)) target :=
      hAl p q z active target m σ
    dsimp only [L]
    rw [h1,h2]
  have hLr : ∀ p q source z active, MarkedRawMemorySymmetric (fun m => L p q source (z,(active,m))) := by
    intro p q source z active m σ
    have h1 : f (z,(active,markedRawMemoryPermute m σ)) = f (z,(active,m)) := hf z active m σ
    have h2 : A p q source (z,(active,markedRawMemoryPermute m σ)) = A p q source (z,(active,m)) :=
      hAr p q source z active m σ
    dsimp only [L]
    rw [h1,h2]
  have h := (markedRawEdge_pattern_full_normalForm ν δ γ hZ L).trans
    ((markedRawEdge_pattern_full_pairing_transpose ν δ γ hZ L hLl hLr).trans
      (markedRawEdge_pattern_full_normalForm ν γ δ hZ (markedRawEdgePatternReverse L)).symm)
  simpa only [markedRawEdgePatternApply, markedRawEdgePatternReverse, L, mul_one,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h

end
end ArtinMatthews
