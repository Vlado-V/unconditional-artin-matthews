module

public import ArtinMatthews.GiantSignedGhostSimultaneous
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Group.Tannery
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

/-! Removing a finite birth-batch frame from the genuine countable
ghost row, using its proved absolute exponential majorant. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {B : Type*} [Fintype B] {P : B → Finset ℕ}

def GiantSignedGhostBatchFits {m : GiantSignedMemory P}
    (H : ℕ) (r : GiantSignedGhostMemoryMoves m) : Prop :=
  ∀ g, (r g).2.1 ≤ H

theorem giantSignedGhostBatchFits_eventually (m : GiantSignedMemory P)
    (r : GiantSignedGhostMemoryMoves m) : ∀ᶠ H : ℕ in atTop, GiantSignedGhostBatchFits H r := by
  filter_upwards [eventually_ge_atTop (∑ g, (r g).2.1)] with H hH
  intro g
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)).trans hH

def giantSignedGhostBatchCutoff (ν : ∀ g, P g → ℝ) (A C D : B → ℂ)
    (f : GiantSignedMemory P → ℂ) (H : ℕ) (m : GiantSignedMemory P) : ℂ :=
  ∑' r : GiantSignedGhostMemoryMoves m,
    if GiantSignedGhostBatchFits H r then
      giantSignedGhostMemoryMoveCoefficient ν A C D m r * f (giantSignedGhostMemoryMoveTarget m r)
    else 0

theorem giantSignedGhostBatchCutoff_summable_norm
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (f : GiantSignedMemory P → ℂ) (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ m, ‖f m‖ ≤ Cf * u ^ (∑ g, m.1 g)) (H : ℕ) (m : GiantSignedMemory P) :
    Summable (fun r : GiantSignedGhostMemoryMoves m =>
      ‖if GiantSignedGhostBatchFits H r then
        giantSignedGhostMemoryMoveCoefficient ν A C D m r * f (giantSignedGhostMemoryMoveTarget m r)
      else 0‖) := by
  apply (giantSignedGhostSimultaneous_summable_norm ν hν A C D f Cf u hCf hu hf m).of_nonneg_of_le
  · intro r
    exact norm_nonneg _
  · intro r
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg
        (giantSignedGhostMemoryMoveCoefficient ν A C D m r * f (giantSignedGhostMemoryMoveTarget m r))

theorem giantSignedGhostBatchCutoff_tendsto
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (f : GiantSignedMemory P → ℂ) (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ m, ‖f m‖ ≤ Cf * u ^ (∑ g, m.1 g)) (m : GiantSignedMemory P) :
    Tendsto (fun H : ℕ => giantSignedGhostBatchCutoff ν A C D f H m) atTop
      (𝓝 (giantSignedGhostSimultaneousApply ν A C D f m)) := by
  unfold giantSignedGhostBatchCutoff giantSignedGhostSimultaneousApply
  apply tendsto_tsum_of_dominated_convergence
    (giantSignedGhostSimultaneous_summable_norm ν hν A C D f Cf u hCf hu hf m)
  · intro r
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [giantSignedGhostBatchFits_eventually m r] with H hH
    exact (ite_eq_left hH).symm
  · exact Filter.Eventually.of_forall fun H r => by
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg
          (giantSignedGhostMemoryMoveCoefficient ν A C D m r * f (giantSignedGhostMemoryMoveTarget m r))

end
end ArtinMatthews
