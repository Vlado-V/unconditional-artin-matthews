module

public import ArtinMatthews.MarkedMemoryPrimeLifespanInterval
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

/-! Boundary and ghost parity of the derived half-step intervals.
In particular, a lifespan reaching the last population is active there,
so the primewise construction ends with empty pending memory. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ} (A : Finset (Fin (N+1))) (c : MarkedMemoryPrimeLifespanChoice N)

theorem markedMemoryPrimeLast_odd_active (v : Fin (N+1))
    (hl : markedMemoryPrimeLast A c=2*v.val+1) : v∈A := by
  cases hb : c.2 with
  | some b => simp only [markedMemoryPrimeLast,hb] at hl; omega
  | none =>
    by_cases hA : A.Nonempty
    · simp only [markedMemoryPrimeLast,hb,dite_eq_left hA] at hl
      have he : A.max' hA=v := Fin.ext (by omega)
      exact he ▸ A.max'_mem hA
    · simp only [markedMemoryPrimeLast,hb,dite_eq_right hA] at hl
      omega

theorem markedMemoryPrimeLast_terminal_active
    (hl : markedMemoryPrimeLast A c=2*N+1) : (Fin.last N)∈A := by
  exact markedMemoryPrimeLast_odd_active A c (Fin.last N) hl

variable {L : Type*} (line : Fin (N+1) → L)

theorem markedMemoryPrimeFirst_ghost_inactive
    (hc : MarkedMemoryPrimeLifespanCompatible line A c) (v : Fin (N+1))
    (hf : markedMemoryPrimeFirst A c=2*v.val+1) : v∉A := by
  intro hv
  have hh := markedMemoryPrimeFirst_active line A c hc v hv
  omega

theorem markedMemoryPrimeLast_ghost_inactive
    (hc : MarkedMemoryPrimeLifespanCompatible line A c) (v : Fin (N+1))
    (hl : markedMemoryPrimeLast A c=2*v.val) : v∉A := by
  intro hv
  have hh := markedMemoryPrimeLast_active line A c hc v hv
  omega

end
end ArtinMatthews
