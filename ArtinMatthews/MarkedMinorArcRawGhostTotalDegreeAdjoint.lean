module

public import ArtinMatthews.MarkedMinorArcRawGhostDegreeChoices
public import ArtinMatthews.MarkedMinorArcRawGhostGroupedDegreeAdjoint
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

/-! Transposing the genuine grouped ghost components with both original
total-memory restrictions retained.  Exchanging deleted and born degrees
is an exact involution of the finite allowed degree family. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Exchange the actual deleted and born degrees, including the two
literal total-memory bounds. -/
def markedRawGhostDegreesSwap {J : Type*} [Fintype J] {B : ℕ} :
    MarkedRawGhostDegrees J B ≃ MarkedRawGhostDegrees J B where
  toFun t := ⟨t.survivors,t.born,t.deleted,t.target_le,t.source_le⟩
  invFun t := ⟨t.survivors,t.born,t.deleted,t.target_le,t.source_le⟩
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

/-- Exact full finite-degree transpose.  Both source and target satisfy
the original sum-of-degrees cutoff, rather than independent per-group
cutoffs.  The functions can couple every prime group. -/
theorem markedRawGhost_total_degree_transpose
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (B : ℕ) (δ γ s : J → ℂ)
    (g f : (k : J → ℕ) → (∑ j,k j) ≤ B →
      ((j : J) → Fin (k j) → MarkedRawParticle (P j)) → ℂ)
    (hg : ∀ k hk,MarkedRawGroupedTupleSymmetric k (g k hk))
    (hf : ∀ k hk,MarkedRawGroupedTupleSymmetric k (f k hk)) :
    (∑ t : MarkedRawGhostDegrees J B,
      ∑ a : (j : J) → Fin (t.survivors j+t.deleted j) → MarkedRawParticle (P j),
        ((∏ j,∏ i,ν j (a j i).1)/(∏ j,(Nat.factorial (t.survivors j+t.deleted j) : ℂ)))*
          g (fun j => t.survivors j+t.deleted j) t.source_le a*
          markedRawGhostGroupedDegreeComponent P ν z hz t.survivors t.deleted t.born δ γ s
            (f (fun j => t.survivors j+t.born j) t.target_le) a)=
      ∑ t : MarkedRawGhostDegrees J B,
        ∑ a : (j : J) → Fin (t.survivors j+t.deleted j) → MarkedRawParticle (P j),
          ((∏ j,∏ i,ν j (a j i).1)/(∏ j,(Nat.factorial (t.survivors j+t.deleted j) : ℂ)))*
            f (fun j => t.survivors j+t.deleted j) t.source_le a*
            markedRawGhostGroupedDegreeComponent P ν z hz t.survivors t.deleted t.born γ δ s
              (g (fun j => t.survivors j+t.born j) t.target_le) a := by
  classical
  rw [← Equiv.sum_comp (markedRawGhostDegreesSwap (J := J) (B := B))]
  apply Finset.sum_congr rfl
  intro t _
  exact markedRawGhost_grouped_degree_transpose P ν z hz
    t.survivors t.born t.deleted δ γ s
      (g _ t.target_le) (hg _ t.target_le) (f _ t.source_le) (hf _ t.source_le)

end ArtinMatthews
