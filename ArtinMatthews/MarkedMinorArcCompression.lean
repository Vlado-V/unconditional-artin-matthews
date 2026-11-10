module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import ArtinMatthews.MarkedMinorArcBlockOperator
public import ArtinMatthews.MarkedMinorArcOperator
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact extension-by-zero and restriction for actual finite L² kernels. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Summation over an injective finite image, with every omitted term zero. -/
theorem markedMinorSum_injective {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid R] (e : κ → ι) (he : Function.Injective e) (f : ι → R)
    (hf : ∀ i, (¬∃ k, e k=i) → f i=0) : ∑ i, f i = ∑ k, f (e k) := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.image e, f i := by
      apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro i _ hi
      apply hf i
      rintro ⟨k,hk⟩
      exact hi (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,hk⟩)
    _ = _ := Finset.sum_image (fun _ _ _ _ h => he h)

/-- The true finite extension by zero preserves counting L² energy. -/
theorem markedMinorExtend_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ → ι) (he : Function.Injective e) (f : κ → ℂ) :
    (∑ i, ‖Function.extend e f 0 i‖^2) = ∑ k, ‖f k‖^2 := by
  classical
  rw [markedMinorSum_injective e he _ (fun i hi => by
    rw [Function.extend_apply' _ _ _ hi]
    simp)]
  simp only [he.extend_apply]

/-- Matrix action on an extension by zero equals action by the literal
submatrix, at every retained output coordinate. -/
theorem markedMinorSubmatrix_injective_mulVec {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (e : κ → ι) (he : Function.Injective e) (f : κ → ℂ) (k : κ) :
    (A *ᵥ Function.extend e f 0) (e k) = (A.submatrix e e *ᵥ f) k := by
  classical
  unfold Matrix.mulVec dotProduct
  rw [markedMinorSum_injective e he _ (fun i hi => by
    rw [Function.extend_apply' _ _ _ hi]
    simp)]
  simp only [he.extend_apply,Matrix.submatrix_apply]

/-- Arbitrary finite principal restriction is a contraction in the genuine
L² operator norm. No factor depends on the support cardinality. -/
theorem markedMinorSubmatrix_injective_norm_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (e : κ → ι) (he : Function.Injective e) :
    ‖A.submatrix e e‖ ≤ ‖A‖ := by
  classical
  apply markedMinorMatrix_norm_le_of_energy _ (norm_nonneg _)
  intro f
  have hh := markedMinorMatrix_energy_le_of_norm A (norm_nonneg _) le_rfl (Function.extend e f 0)
  rw [markedMinorExtend_energy e he f] at hh
  calc
    _ = ∑ k, ‖(A *ᵥ Function.extend e f 0) (e k)‖^2 := by
      simp only [markedMinorSubmatrix_injective_mulVec A e he f]
    _ = ∑ i ∈ Finset.univ.image e, ‖(A *ᵥ Function.extend e f 0) i‖^2 :=
      (Finset.sum_image (s := Finset.univ) (g := e)
        (f := fun i => ‖(A *ᵥ Function.extend e f 0) i‖^2)
        (fun _ _ _ _ h => he h)).symm
    _ ≤ ∑ i, ‖(A *ᵥ Function.extend e f 0) i‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := hh

end ArtinMatthews
