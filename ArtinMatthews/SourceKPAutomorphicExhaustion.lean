module

public import ArtinMatthews.SourceKPCompactHeight
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

namespace ArtinMatthews
open NumberField Filter
open scoped NumberField MatrixGroups AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAutomorphicExhaustionCutoff (n : ℕ) (x : SourceKPAutomorphicCompactLevel K hζ) : ℝ :=
  1 - Real.smoothTransition
    (Real.log (sourceKPAutomorphicCompactOrbitHeight K hζ x) - ((n : ℝ) + 1))

theorem sourceKPAutomorphicExhaustionCutoff_nonneg (n : ℕ)
    (x : SourceKPAutomorphicCompactLevel K hζ) :
    0 ≤ sourceKPAutomorphicExhaustionCutoff K hζ n x := by
  unfold sourceKPAutomorphicExhaustionCutoff
  linarith [Real.smoothTransition.le_one
    (Real.log (sourceKPAutomorphicCompactOrbitHeight K hζ x) - ((n : ℝ) + 1))]

theorem sourceKPAutomorphicExhaustionCutoff_le_one (n : ℕ)
    (x : SourceKPAutomorphicCompactLevel K hζ) :
    sourceKPAutomorphicExhaustionCutoff K hζ n x ≤ 1 := by
  unfold sourceKPAutomorphicExhaustionCutoff
  linarith [Real.smoothTransition.nonneg
    (Real.log (sourceKPAutomorphicCompactOrbitHeight K hζ x) - ((n : ℝ) + 1))]

theorem sourceKPAutomorphicExhaustionCutoff_eq_one (n : ℕ)
    (x : SourceKPAutomorphicCompactLevel K hζ)
    (hx : Real.log (sourceKPAutomorphicCompactOrbitHeight K hζ x) ≤ (n : ℝ) + 1) :
    sourceKPAutomorphicExhaustionCutoff K hζ n x = 1 := by
  unfold sourceKPAutomorphicExhaustionCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

theorem sourceKPAutomorphicExhaustionCutoff_eq_zero (n : ℕ)
    (x : SourceKPAutomorphicCompactLevel K hζ)
    (hx : Real.exp ((n : ℝ) + 2) ≤ sourceKPAutomorphicCompactOrbitHeight K hζ x) :
    sourceKPAutomorphicExhaustionCutoff K hζ n x = 0 := by
  have hlog := Real.log_le_log (Real.exp_pos ((n : ℝ) + 2)) hx
  rw [Real.log_exp] at hlog
  unfold sourceKPAutomorphicExhaustionCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem sourceKPAutomorphicExhaustionCutoff_hasCompactSupport (n : ℕ) :
    HasCompactSupport (sourceKPAutomorphicExhaustionCutoff K hζ n) := by
  have hs : Function.support (sourceKPAutomorphicExhaustionCutoff K hζ n) ⊆
      {x | sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ Real.exp ((n : ℝ) + 2)} := by
    intro x hx
    by_contra h
    exact hx (sourceKPAutomorphicExhaustionCutoff_eq_zero K hζ n x (lt_of_not_ge h).le)
  have hclosed : IsClosed {x | sourceKPAutomorphicCompactOrbitHeight K hζ x ≤
      Real.exp ((n : ℝ) + 2)} :=
    (lowerSemicontinuous_iff_isClosed_preimage.mp
      (sourceKPAutomorphicCompactOrbitHeight_lowerSemicontinuous K hζ)) _
  exact (sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ _).of_isClosed_subset
    isClosed_closure (closure_minimal hs hclosed)

theorem sourceKPAutomorphicExhaustionCutoff_monotone
    (x : SourceKPAutomorphicCompactLevel K hζ) :
    Monotone (fun n => sourceKPAutomorphicExhaustionCutoff K hζ n x) := by
  intro n m hnm
  have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have h := Real.smoothTransition.monotone (show
    Real.log (sourceKPAutomorphicCompactOrbitHeight K hζ x) - ((m : ℝ) + 1) ≤
    Real.log (sourceKPAutomorphicCompactOrbitHeight K hζ x) - ((n : ℝ) + 1) by linarith)
  unfold sourceKPAutomorphicExhaustionCutoff
  linarith

theorem sourceKPAutomorphicExhaustionCutoff_eventually_one
    (x : SourceKPAutomorphicCompactLevel K hζ) :
    ∀ᶠ n : ℕ in atTop, sourceKPAutomorphicExhaustionCutoff K hζ n x = 1 := by
  obtain ⟨N,hN⟩ := exists_nat_ge (Real.log (sourceKPAutomorphicCompactOrbitHeight K hζ x))
  filter_upwards [eventually_ge_atTop N] with n hn
  apply sourceKPAutomorphicExhaustionCutoff_eq_one
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

end
end ArtinMatthews
