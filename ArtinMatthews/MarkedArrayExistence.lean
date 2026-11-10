module

public import Mathlib.Algebra.Group.End
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! A concrete supply of arbitrarily many finite disjoint marking arrays. -/

namespace ArtinMatthews

noncomputable def markedDistinctExponent {J I : Type*} [Fintype J] [Fintype I]
    (j : J) (i : I) : ℝ :=
  1 / 10 + (((Fintype.equivFin (J × I) (j, i)).val : ℝ) + 1) /
    (10 * ((Fintype.card (J × I) : ℝ) + 1))

theorem markedDistinctExponent_range {J I : Type*} [Fintype J] [Fintype I]
    (j : J) (i : I) :
    (1 / 10 : ℝ) < markedDistinctExponent j i ∧ markedDistinctExponent j i < 1 / 5 := by
  have hn : (0 : ℝ) < 10 * ((Fintype.card (J × I) : ℝ) + 1) := by positivity
  have hi : (((Fintype.equivFin (J × I) (j, i)).val : ℝ) + 1) <
      (Fintype.card (J × I) : ℝ) + 1 := by
    have := (Fintype.equivFin (J × I) (j, i)).isLt
    exact_mod_cast (Nat.add_lt_add_right this 1)
  dsimp [markedDistinctExponent]
  constructor
  · have : 0 < (((Fintype.equivFin (J × I) (j, i)).val : ℝ) + 1) /
        (10 * ((Fintype.card (J × I) : ℝ) + 1)) := div_pos (by positivity) hn
    linarith
  · have hq : (((Fintype.equivFin (J × I) (j, i)).val : ℝ) + 1) /
        (10 * ((Fintype.card (J × I) : ℝ) + 1)) < 1 / 10 := by
      apply (div_lt_iff₀ hn).2
      linarith
    linarith

theorem markedDistinctExponent_injective {J I : Type*} [Fintype J] [Fintype I] :
    Function.Injective (fun ji : J × I => markedDistinctExponent ji.1 ji.2) := by
  intro a b hab
  have hn : (10 * ((Fintype.card (J × I) : ℝ) + 1)) ≠ 0 := by positivity
  have hq : (((Fintype.equivFin (J × I) a).val : ℝ) + 1) /
      (10 * ((Fintype.card (J × I) : ℝ) + 1)) =
      (((Fintype.equivFin (J × I) b).val : ℝ) + 1) /
      (10 * ((Fintype.card (J × I) : ℝ) + 1)) := by
    simpa only [markedDistinctExponent, add_right_inj, Prod.mk.eta] using hab
  have hr := (div_left_inj' hn).1 hq
  have hv : (Fintype.equivFin (J × I) a).val = (Fintype.equivFin (J × I) b).val := by
    exact_mod_cast (add_right_cancel hr)
  exact (Fintype.equivFin (J × I)).injective (Fin.ext hv)

/-- Any prescribed finite numbers of arrays and bands admit pairwise distinct
exponents in the permitted interval. Empty index types are allowed. -/
theorem exists_marked_disjoint_arrays (B K : ℕ) :
    ∃ e : Fin B → Fin K → ℝ,
      (∀ j i, (1 / 10 : ℝ) < e j i ∧ e j i < 1 / 5) ∧
      Function.Injective (fun ji : Fin B × Fin K => e ji.1 ji.2) :=
  ⟨markedDistinctExponent, markedDistinctExponent_range, markedDistinctExponent_injective⟩

end ArtinMatthews
