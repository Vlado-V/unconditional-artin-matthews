module

public import ArtinMatthews.MarkedArrayExpansion
public import ArtinMatthews.MarkedProgressionWeightedModel
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

/-! The exact represented-sum Euler mean and normalized coefficients used
when transferring the actual marking weights to progressions. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable def representedArraySelected {ι : Type*} [Fintype ι] {a : ι → ℕ}
    (t : (i : ι) → Fin (a i) → ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun i => representedChoiceSet (t i))

noncomputable def representedArrayCoefficient {ι : Type*} [Fintype ι]
    (V : ι → ℝ) (a : ι → ℕ) (t : (i : ι) → Fin (a i) → ℕ) : ℝ :=
  (∏ i, (1 / 2 : ℝ) ^ (a i * ((representedChoiceSet (t i)).card - 1))) /
    (∏ i, V i ^ a i)

noncomputable def representedArrayEulerMean {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (V : ι → ℝ) (a : ι → ℕ) : ℝ :=
  ∑ t ∈ representedArrayChoices P a, representedArrayCoefficient V a t *
    markedWeightedModel (Finset.univ.biUnion P) (representedArraySelected t)
      (representedArrayDamping Finset.univ P a (1 / 2))

/-- The actual arithmetic array is precisely the normalized finite family
of selected residuals whose Euler mean was defined above. -/
theorem bandWeight_product_powers_eq_normalized_residual_sum {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (V : ι → ℝ) (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) (u : ℕ) :
    (∏ i, (bandWeight (P i) (V i) u) ^ a i) =
      ∑ t ∈ representedArrayChoices P a, representedArrayCoefficient V a t *
        markedWeightedResidual (Finset.univ.biUnion P) (representedArraySelected t)
          (representedArrayDamping Finset.univ P a (1 / 2)) u := by
  classical
  rw [bandWeight_product_powers_eq_union_residual_sum P V a ha hdis u, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  unfold representedArrayCoefficient representedArraySelected
  ring

end ArtinMatthews
