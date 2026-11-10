module

public import ArtinMatthews.MarkedMinorArcRawGhostAbsoluteAction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact action of the literal positive ghost kernels on their actual
Schur weight. These identities retain every indexed choice and the total
birth cutoff; the weighted rows are the previously bounded concrete sums. -/
namespace ArtinMatthews
open scoped BigOperators

theorem markedRawMemorySchurWeight_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (v₀ : ℝ) (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) :
    markedRawMemorySchurWeight v₀ (markedRawMemoryPermute m σ)=
      markedRawMemorySchurWeight v₀ m := rfl

/-- The original positive action on the true Schur weight is exactly
the literal weighted row times the input weight. -/
theorem markedRawGhostAbsApply_schur {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (V : J → ℝ) (qStage ρ : ℝ) {v₀ : ℝ} (hv₀ : 0 < v₀)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (s : MarkedRawState P M B Z) :
    markedRawGhostAbsApply ν V qStage ρ hZ
      (fun t => (markedRawMemorySchurWeight v₀ t.2.2 : ℂ)) s=
        ((markedRawGhostWeightedAbsRow ν V qStage ρ v₀ s.2.2 s.1.1 (hZ _ s.1.2)*
          markedRawMemorySchurWeight v₀ s.2.2 : ℝ) : ℂ) := by
  classical
  have hw : (markedRawMemorySchurWeight v₀ s.2.2 : ℂ) ≠ 0 := by
    exact_mod_cast (markedRawMemorySchurWeight_pos hv₀ s.2.2).ne'
  unfold markedRawGhostAbsApply markedRawGhostWeightedAbsRow
  simp only [Finset.sum_mul,ite_mul,zero_mul,Complex.ofReal_sum,apply_ite,
    Complex.ofReal_zero,Complex.ofReal_mul,Complex.ofReal_div]
  apply Finset.sum_congr rfl
  intro del _
  split_ifs
  · apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro births _
    change _ * (markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory s.2.2 s.1.1
      (hZ _ s.1.2) del l births) : ℂ)=_
    field_simp
  · rfl

/-- The swapped positive action has exactly its own literal weighted
row, against the same original memory weight. -/
theorem markedRawGhostSwappedAbsApply_schur {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (V : J → ℝ) (qStage ρ : ℝ) {v₀ : ℝ} (hv₀ : 0 < v₀)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (s : MarkedRawState P M B Z) :
    markedRawGhostSwappedAbsApply ν V qStage ρ hZ
      (fun t => (markedRawMemorySchurWeight v₀ t.2.2 : ℂ)) s=
        ((markedRawGhostSwappedWeightedAbsRow ν V qStage ρ v₀ s.2.2 s.1.1 (hZ _ s.1.2)*
          markedRawMemorySchurWeight v₀ s.2.2 : ℝ) : ℂ) := by
  classical
  have hw : (markedRawMemorySchurWeight v₀ s.2.2 : ℂ) ≠ 0 := by
    exact_mod_cast (markedRawMemorySchurWeight_pos hv₀ s.2.2).ne'
  unfold markedRawGhostSwappedAbsApply markedRawGhostSwappedWeightedAbsRow
  simp only [Finset.sum_mul,ite_mul,zero_mul,Complex.ofReal_sum,apply_ite,
    Complex.ofReal_zero,Complex.ofReal_mul,Complex.ofReal_div]
  apply Finset.sum_congr rfl
  intro del _
  split_ifs
  · apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro births _
    change _ * (markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory s.2.2 s.1.1
      (hZ _ s.1.2) del l births) : ℂ)=_
    field_simp
  · rfl

end ArtinMatthews
