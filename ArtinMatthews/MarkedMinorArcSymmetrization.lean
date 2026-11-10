module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import ArtinMatthews.MarkedMinorArcBlockOperator
public import ArtinMatthews.MarkedMinorArcOperator
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

/-! Actual independent left and right finite slot symmetrizations are L²
contractions. The two permutations need not be equal. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem markedMinorMatrix_submatrix_equiv_pair_norm_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (e f : κ ≃ ι) : ‖A.submatrix e f‖ ≤ ‖A‖ := by
  apply markedMinorMatrix_norm_le_of_energy _ (norm_nonneg _)
  intro g
  rw [Matrix.submatrix_mulVec_equiv A g e f]
  calc
    _ = ∑ i : ι, ‖(A *ᵥ (g ∘ f.symm)) i‖^2 :=
      e.sum_comp (fun i => ‖(A *ᵥ (g ∘ f.symm)) i‖^2)
    _ ≤ ‖A‖^2 * ∑ i : ι, ‖(g ∘ f.symm) i‖^2 :=
      markedMinorMatrix_energy_le_of_norm A (norm_nonneg _) le_rfl _
    _ = _ := by
      rw [← f.sum_comp (fun i => ‖(g ∘ f.symm) i‖^2)]
      simp only [Function.comp_apply,Equiv.symm_apply_apply]

/-- Independent finite row and column reindexings preserve the actual norm. -/
theorem markedMinorMatrix_submatrix_equiv_pair_norm {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (e f : κ ≃ ι) : ‖A.submatrix e f‖ = ‖A‖ := by
  apply le_antisymm (markedMinorMatrix_submatrix_equiv_pair_norm_le A e f)
  have hh := markedMinorMatrix_submatrix_equiv_pair_norm_le (A.submatrix e f) e.symm f.symm
  have he : (A.submatrix e f).submatrix e.symm f.symm=A := by ext i j; simp
  rwa [he] at hh

/-- Any actual probability average of independently reindexed kernels is
an L² contraction; this includes the source S*T*S slot averages. -/
theorem markedMinorMatrix_average_slotPairs_norm_le {ι J : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J]
    (A : Matrix ι ι ℂ) (e f : J → Equiv.Perm ι) (weight : J → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hmass : ∑ j, weight j=1) :
    ‖∑ j, (weight j) • A.submatrix (e j) (f j)‖ ≤ ‖A‖ := by
  calc
    _ ≤ ∑ j, ‖(weight j) • A.submatrix (e j) (f j)‖ := norm_sum_le _ _
    _ = ∑ j, weight j*‖A‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_smul,Real.norm_of_nonneg (hw j),markedMinorMatrix_submatrix_equiv_pair_norm]
    _ = _ := by rw [← Finset.sum_mul,hmass,one_mul]

end ArtinMatthews
