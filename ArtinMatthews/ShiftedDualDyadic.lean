module

public import ArtinMatthews.SpectralDyadicReassembly
public import ArtinMatthews.ShiftedDualSplit
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

/-! Exact, absolutely convergent dyadic reassembly of the nonzero-frequency
Kloosterman dual. No cancellation estimate is assumed in this decomposition. -/
noncomputable section
namespace ArtinMatthews
open scoped BigOperators

lemma shiftedDualNonzeroTerm_fst_pos (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (ha0 : a 0 = 0) (k : ℕ × ℕ)
    (hk : shiftedDualNonzeroTerm q D m3 m4 a b k ≠ 0) : 1 ≤ k.1 := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro h
  apply hk
  simp [shiftedDualNonzeroTerm, shiftedDualTerm, h, ha0]

lemma shiftedDualNonzeroTerm_snd_pos (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (hb0 : b 0 = 0) (k : ℕ × ℕ)
    (hk : shiftedDualNonzeroTerm q D m3 m4 a b k ≠ 0) : 1 ≤ k.2 := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro h
  apply hk
  simp [shiftedDualNonzeroTerm, shiftedDualTerm, h, hb0]

theorem shiftedDualNonzero_dyadic_summable (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (ha : Summable a) (hb : Summable b)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) :
    Summable (fun z : (ℕ × ℕ) × (ℕ × ℕ) =>
      spectralDyadicCoefficient (shiftedDualNonzeroTerm q D m3 m4 a b z.1)
        z.1.1 z.1.2 z.2) :=
  spectralDyadic_expansion_summable _ Prod.fst Prod.snd
    (shiftedDualNonzeroTerm_summable q D m3 m4 a b ha hb)
    (shiftedDualNonzeroTerm_fst_pos q D m3 m4 a b ha0)
    (shiftedDualNonzeroTerm_snd_pos q D m3 m4 a b hb0)

theorem shiftedDualNonzero_dyadic_reassembly (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (ha : Summable a) (hb : Summable b)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) :
    (∑' k, shiftedDualNonzeroTerm q D m3 m4 a b k) =
      ∑' d : ℕ × ℕ, ∑' k : ℕ × ℕ,
        spectralDyadicCoefficient (shiftedDualNonzeroTerm q D m3 m4 a b k)
          k.1 k.2 d :=
  spectralDyadic_reassembly _ Prod.fst Prod.snd
    (shiftedDualNonzeroTerm_summable q D m3 m4 a b ha hb)
    (shiftedDualNonzeroTerm_fst_pos q D m3 m4 a b ha0)
    (shiftedDualNonzeroTerm_snd_pos q D m3 m4 a b hb0)

theorem shiftedDualNonzero_dyadic_norm (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (ha : Summable a) (hb : Summable b)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) :
    (∑' z : (ℕ × ℕ) × (ℕ × ℕ),
      ‖spectralDyadicCoefficient (shiftedDualNonzeroTerm q D m3 m4 a b z.1)
        z.1.1 z.1.2 z.2‖) = ∑' k, ‖shiftedDualNonzeroTerm q D m3 m4 a b k‖ :=
  spectralDyadic_norm_reassembly _ Prod.fst Prod.snd
    (shiftedDualNonzeroTerm_summable q D m3 m4 a b ha hb)
    (shiftedDualNonzeroTerm_fst_pos q D m3 m4 a b ha0)
    (shiftedDualNonzeroTerm_snd_pos q D m3 m4 a b hb0)

end ArtinMatthews
