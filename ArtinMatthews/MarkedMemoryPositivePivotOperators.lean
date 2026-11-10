module

public import ArtinMatthews.MarkedMemoryConditionalGhostRow
public import ArtinMatthews.MarkedMemoryConditionalEdgeRow
public import ArtinMatthews.MarkedMemoryEdgePivotMass
public import ArtinMatthews.MarkedMemoryGhostPivotMass
public import ArtinMatthews.MarkedMemoryPivotValueDefs
public import ArtinMatthews.MarkedWeightedConditionalKernel
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

/-! Positive chronological operators with the actual pivot memo update.
They are used only for the high-rank absolute estimate; the low-rank
argument retains the signed operators. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryPositiveGhostPivot
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ)
    {M B N slots : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin (N+1))
    (f : (MarkedMemoryPotentialAddress J M B N → Option Nat.Primes) → MarkedRawState P slots B Z → ℝ)
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (s : MarkedRawState P slots B Z) : ℝ :=
  ∑ c : MarkedMemoryGhostChoice hZ s,
    if markedMemoryGhostPivotGate σ t old c.sizes.1 c.births then
      ‖markedMemoryGhostChoiceWeight ν V qStage ρ hZ s c‖*
        f (markedMemoryGhostPivotValues t old c.sizes.1 c.births) (markedMemoryGhostChoiceTarget hZ s c)
    else 0

def markedMemoryPositiveEdgePivot
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {M B N pads : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin N)
    (f : (MarkedMemoryPotentialAddress J M B N → Option Nat.Primes) → MarkedRawState P (pads+1) B Z → ℝ)
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (s : MarkedRawState P (pads+1) B Z) : ℝ :=
  ∑ c : MarkedMemoryEdgeChoice hZ s,
    if markedMemoryEdgePivotGate σ t old hZ (markedRawSlotEquiv c.1 s) c.2.1 then
      ‖markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s c‖*
        f (markedMemoryEdgePivotValues t old hZ (markedRawSlotEquiv c.1 s) c.2.1)
          (markedMemoryEdgeChoiceTarget hZ s c)
    else 0

theorem markedMemoryPositiveGhostPivot_bound
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ v₀ : ℝ)
    {M B N slots : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin (N+1))
    (f : (MarkedMemoryPotentialAddress J M B N → Option Nat.Primes) → MarkedRawState P slots B Z → ℝ)
    {C R : ℝ} (hC : 0 ≤ C) (hv₀ : 0 < v₀)
    (hf : ∀ old s,f old s ≤ C*markedRawMemorySchurWeight v₀ s.2.2)
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (s : MarkedRawState P slots B Z)
    (hrow : markedMemoryConditionalGhostRow ν V qStage ρ v₀ hZ s
      (fun _ l births => markedMemoryGhostPivotGate σ t old l.1 births) ≤ R) :
    markedMemoryPositiveGhostPivot ν V qStage ρ hZ σ t f old s ≤
      C*R*markedRawMemorySchurWeight v₀ s.2.2 := by
  let K := fun c : MarkedMemoryGhostChoice hZ s =>
    if markedMemoryGhostPivotGate σ t old c.sizes.1 c.births then
      ‖markedMemoryGhostChoiceWeight ν V qStage ρ hZ s c‖ else 0
  have hK (c) : 0 ≤ K c := by dsimp [K]; split_ifs <;> positivity
  have hr : (∑ c : MarkedMemoryGhostChoice hZ s,
      K c*markedRawMemorySchurWeight v₀ (markedMemoryGhostChoiceTarget hZ s c).2.2/
        markedRawMemorySchurWeight v₀ s.2.2) ≤ R := by
    simpa only [K,ite_mul,zero_mul,ite_div,zero_div,markedMemoryConditionalGhostRow,div_eq_mul_inv,mul_assoc] using hrow
  have h := markedWeightedConditionalKernel_bound K
    (fun c => markedRawMemorySchurWeight v₀ (markedMemoryGhostChoiceTarget hZ s c).2.2)
    (fun c => f (markedMemoryGhostPivotValues t old c.sizes.1 c.births) (markedMemoryGhostChoiceTarget hZ s c))
    (markedRawMemorySchurWeight_pos hv₀ _) hC hK (fun c => hf _ _) hr
  simpa only [K,ite_mul,zero_mul,markedMemoryPositiveGhostPivot] using h

theorem markedMemoryPositiveEdgePivot_bound
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {M B N pads : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin N)
    (f : (MarkedMemoryPotentialAddress J M B N → Option Nat.Primes) → MarkedRawState P (pads+1) B Z → ℝ)
    {C R : ℝ} (hC : 0 ≤ C) (hv₀ : 0 < v₀)
    (hf : ∀ old s,f old s ≤ C*markedRawMemorySchurWeight v₀ s.2.2)
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (s : MarkedRawState P (pads+1) B Z)
    (hrow : markedMemoryConditionalEdgeRow ν V hZ ψ η d₀ Y Q ρ v₀ χ
      (fun s => markedMemoryEdgePivotGate σ t old hZ s) s ≤ R) :
    markedMemoryPositiveEdgePivot ν V hZ ψ η d₀ Y Q ρ χ σ t f old s ≤
      C*R*markedRawMemorySchurWeight v₀ s.2.2 := by
  let K := fun c : MarkedMemoryEdgeChoice hZ s =>
    if markedMemoryEdgePivotGate σ t old hZ (markedRawSlotEquiv c.1 s) c.2.1 then
      ‖markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s c‖ else 0
  have hK (c) : 0 ≤ K c := by dsimp [K]; split_ifs <;> positivity
  have hr : (∑ c : MarkedMemoryEdgeChoice hZ s,
      K c*markedRawMemorySchurWeight v₀ (markedMemoryEdgeChoiceTarget hZ s c).2.2/
        markedRawMemorySchurWeight v₀ s.2.2) ≤ R := by
    simpa only [K,ite_mul,zero_mul,ite_div,zero_div,markedMemoryConditionalEdgeRow,div_eq_mul_inv,mul_assoc] using hrow
  have h := markedWeightedConditionalKernel_bound K
    (fun c => markedRawMemorySchurWeight v₀ (markedMemoryEdgeChoiceTarget hZ s c).2.2)
    (fun c => f (markedMemoryEdgePivotValues t old hZ (markedRawSlotEquiv c.1 s) c.2.1)
      (markedMemoryEdgeChoiceTarget hZ s c))
    (markedRawMemorySchurWeight_pos hv₀ _) hC hK (fun c => hf _ _) hr
  simpa only [K,ite_mul,zero_mul,markedMemoryPositiveEdgePivot] using h

end ArtinMatthews
