module

public import ArtinMatthews.FixedURootCount
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The counted congruence pairs are actual primitive first columns with
integral determinant-one completions and the prescribed completion residue. -/
namespace ArtinMatthews
open OAI.Erdos970 ErdosHyperbolaError

/-- Every counted pair has an actual determinant-one integer completion. -/
theorem fixedURootPairs_completion {u S : ℕ} {c₀ v₀ d₀ : ℤ}
    {x₀ x₁ y₀ y₁ : ℝ} {lcI rcI lcJ rcJ : Bool} {c v : ℤ}
    (hmem : (c,v) ∈ fixedURootPairs u S c₀ v₀ d₀ x₀ x₁ y₀ y₁ lcI rcI lcJ rcJ) :
    ∃ d : ℤ, (u : ℤ)*d-v*c = 1 ∧ Int.ModEq (S : ℤ) d d₀ := by
  have hp := (Finset.mem_filter.mp hmem).2.2.2
  exact (fixedURoot_completion_iff u S c v d₀).mp hp

/-- The determinant-one completion is unique for positive first coordinate. -/
theorem fixedURootPairs_completion_unique {u S : ℕ} (hu : 0 < u) {c₀ v₀ d₀ : ℤ}
    {x₀ x₁ y₀ y₁ : ℝ} {lcI rcI lcJ rcJ : Bool} {c v : ℤ}
    (hmem : (c,v) ∈ fixedURootPairs u S c₀ v₀ d₀ x₀ x₁ y₀ y₁ lcI rcI lcJ rcJ) :
    ∃! d : ℤ, (u : ℤ)*d-v*c = 1 ∧ Int.ModEq (S : ℤ) d d₀ := by
  obtain ⟨d,hd⟩ := fixedURootPairs_completion hmem
  refine ⟨d,hd,?_⟩
  intro e he
  apply mul_left_cancel₀ (show (u : ℤ) ≠ 0 by exact_mod_cast hu.ne')
  linarith [he.1,hd.1]

/-- The counted first column is primitive; this is a consequence of its
completion, rather than an extra filtering assumption. -/
theorem fixedURootPairs_first_column_coprime {u S : ℕ} {c₀ v₀ d₀ : ℤ}
    {x₀ x₁ y₀ y₁ : ℝ} {lcI rcI lcJ rcJ : Bool} {c v : ℤ}
    (hmem : (c,v) ∈ fixedURootPairs u S c₀ v₀ d₀ x₀ x₁ y₀ y₁ lcI rcI lcJ rcJ) :
    u.Coprime v.natAbs := by
  obtain ⟨d,hd,_⟩ := fixedURootPairs_completion hmem
  have hc : IsCoprime (u : ℤ) v := by
    refine ⟨d,-c,?_⟩
    linear_combination hd
  apply Nat.coprime_iff_gcd_eq_one.mpr
  simpa only [Int.gcd_def,Int.natAbs_natCast] using
    (Int.isCoprime_iff_gcd_eq_one.mp hc)

end ArtinMatthews
