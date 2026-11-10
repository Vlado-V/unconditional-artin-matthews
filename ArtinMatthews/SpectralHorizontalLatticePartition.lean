module

public import ArtinMatthews.SpectralHorizontalPeriodPartition
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact horizontal window sums to one under every integer
multiple of its period.  No period-one normalization is introduced. -/

noncomputable section
open Set
open scoped BigOperators

namespace ArtinMatthews

theorem spectralHorizontalPartition_finsum_on_period {w x : ℝ} (hw : 0 < w)
    (hx : x ∈ Icc 0 w) :
    (∑ᶠ k : ℤ, spectralHorizontalPartition w (x + w * k)) = 1 := by
  classical
  have hs : Function.support (fun k : ℤ => spectralHorizontalPartition w (x + w * k)) ⊆
      ({0,1} : Finset ℤ) := by
    intro k hk
    by_contra hnot
    have hki : k ≤ -1 ∨ 2 ≤ k := by
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hnot
      omega
    change spectralHorizontalPartition w (x + w * k) ≠ 0 at hk
    rcases hki with hki | hki
    · have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast hki
      exact hk (spectralHorizontalPartition_zero_left hw (by nlinarith [hx.2]))
    · have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hki
      exact hk (spectralHorizontalPartition_zero_right hw (by nlinarith [hx.1]))
  calc
    _ = spectralHorizontalPartition w x + spectralHorizontalPartition w (x + w) := by
      rw [finsum_eq_sum_of_support_subset _ hs]
      simp
    _ = 1 := spectralHorizontalPartition_add_shift hw hx

theorem spectralHorizontalPartition_lattice_finsum {w : ℝ} (hw : 0 < w) (x : ℝ) :
    (∑ᶠ k : ℤ, spectralHorizontalPartition w (x + w * k)) = 1 := by
  let k : ℤ := Int.floor (x / w)
  let y : ℝ := x - w * k
  have hklo : (k : ℝ) ≤ x / w := Int.floor_le _
  have hkhi : x / w < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hy : y ∈ Icc 0 w := by
    constructor
    · have h := (le_div_iff₀ hw).mp hklo
      dsimp [y]
      nlinarith
    · have h := (div_lt_iff₀ hw).mp hkhi
      dsimp [y]
      nlinarith
  calc
    _ = ∑ᶠ j : ℤ, spectralHorizontalPartition w (y + w * (j + k)) := by
      congr 1
      funext j
      congr 1
      dsimp [y]
      ring
    _ = ∑ᶠ j : ℤ, spectralHorizontalPartition w (y + w * j) := by
      simpa using (finsum_comp_equiv
        (f := fun j : ℤ => spectralHorizontalPartition w (y + w * j)) (Equiv.addRight k))
    _ = 1 := spectralHorizontalPartition_finsum_on_period hw hy

end ArtinMatthews
