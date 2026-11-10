module

public import ArtinMatthews.SpectralCuspDoubleCosetRepresentatives
public import ArtinMatthews.SpectralPoincareGeometricKernel
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Exact fixed-positive-modulus reindexing of the actual compact geometric
kernel, retaining the common period N and both integer translation factors. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace Pointwise BigOperators

namespace ArtinMatthews

theorem compactPoincareGeometricKernel_all_hasFiniteSupport (ψ φ : h2SmoothCompactSeeds) :
    Function.HasFiniteSupport (compactPoincareGeometricKernel ψ φ) := by
  apply (integer_compact_translates_finite ψ.val.hasCompactSupport φ.val.hasCompactSupport).subset
  intro M hM
  by_contra hnot
  apply hM
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  simp only [Pi.zero_apply]
  by_cases hz : ψ.val z = 0
  · rw [hz,inner_zero_left]
  have hφ : φ.val (M • z) = 0 := by
    by_contra hφ
    exact hnot ⟨M • z, ⟨⟨z,subset_tsupport _ hz,rfl⟩,subset_tsupport _ hφ⟩⟩
  rw [hφ,inner_zero_right]

theorem compactPoincareDoubleCoset_hasFiniteSupport (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (ψ φ : h2SmoothCompactSeeds) :
    Function.HasFiniteSupport (fun p : gamma0CuspReducedMatrix N r s c × ℤ × ℤ =>
      compactPoincareGeometricKernel ψ φ (gamma0CuspDoubleCosetExpand N r s c p).val) := by
  apply Function.HasFiniteSupport.fun_comp_of_injective
    (g := fun p : gamma0CuspReducedMatrix N r s c × ℤ × ℤ =>
      (gamma0CuspDoubleCosetExpand N r s c p).val)
  · exact Subtype.val_injective.comp (gamma0CuspDoubleCosetExpand_injective N r s c)
  · exact compactPoincareGeometricKernel_all_hasFiniteSupport ψ φ

theorem compactPoincareGeometricKernel_double_coset_sum (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (ψ φ : h2SmoothCompactSeeds) :
    (∑ᶠ M : gamma0CuspMatrixFibre N r s c, compactPoincareGeometricKernel ψ φ M.val) =
      ∑ R : gamma0CuspReducedMatrix N r s c, ∑ᶠ p : ℤ × ℤ,
        compactPoincareGeometricKernel ψ φ
          (integerTranslation ((N : ℤ) * p.1) * R.val * integerTranslation ((N : ℤ) * p.2)) := by
  rw [← gamma0CuspDoubleCoset_finsum N r s c]
  rw [finsum_curry _ (compactPoincareDoubleCoset_hasFiniteSupport N r s c ψ φ),
    finsum_eq_sum_of_fintype]
  rfl

theorem gamma0CuspReducedMatrix_card_le (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Fintype.card (gamma0CuspReducedMatrix N r s c) ≤ (N * c) ^ 2 := by
  have h := Fintype.card_le_of_injective _ (gamma0CuspReducedMatrix_diagonal_injective N r s c)
  simpa only [Fintype.card_prod, ZMod.card, pow_two] using h

end ArtinMatthews
