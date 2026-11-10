module

public import ArtinMatthews.SourceArchScatteringGram
public import ArtinMatthews.SourceArchSphericalUnitary
public import OAI.NumberTheory.DirichletL.Eisenstein.Rows
public import ArtinMatthews.SourceArchCoordinateCasimir
public import ArtinMatthews.SourceArchSphericalContinuity
public import ArtinMatthews.SourceKPCommRingDiagonal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual scalar and unitary invariant Gram coordinates in upper half-space. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup OAI.CubicEisenstein
open scoped MatrixGroups
noncomputable section

abbrev SourceArchUpperHalfSpace := ℂ × {y : ℝ // 0 < y}

def sourceArchGramCoordinates (g : GL (Fin 2) ℂ) : SourceArchUpperHalfSpace :=
  (sourceArchGramShift g, ⟨sourceArchHeight g, sourceArchHeight_pos g⟩)

theorem sourceArchGramShift_eq_gram (g : GL (Fin 2) ℂ) :
    sourceArchGramShift g =
      (((g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ)) 0 1) /
      (((g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ)) 1 1) := by
  rw [← sourceArchBottomNorm_gram]
  simp only [sourceArchGramShift, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

theorem sourceArchGramShift_continuous : Continuous sourceArchGramShift := by
  apply Continuous.div ?_ (Complex.continuous_ofReal.comp sourceArchBottomNorm_continuous)
    (fun g => Complex.ofReal_ne_zero.mpr (sourceArchBottomNorm_pos g).ne')
  exact ((sourceArchMatrixEntry_continuous 0 0).mul
    (continuous_star.comp (sourceArchMatrixEntry_continuous 1 0))).add
      ((sourceArchMatrixEntry_continuous 0 1).mul
        (continuous_star.comp (sourceArchMatrixEntry_continuous 1 1)))

theorem sourceArchGramCoordinates_continuous : Continuous sourceArchGramCoordinates :=
  sourceArchGramShift_continuous.prodMk (sourceArchHeight_continuous.subtype_mk _)

theorem sourceArchGramShift_scalar (g : GL (Fin 2) ℂ) (u : ℂˣ) :
    sourceArchGramShift (g * GeneralLinearGroup.scalar (Fin 2) u) = sourceArchGramShift g := by
  have hu : (u : ℂ) * star (u : ℂ) = (‖(u : ℂ)‖ ^ 2 : ℝ) := by
    simpa only [Complex.star_def, Complex.ofReal_pow] using (Complex.mul_conj' (u : ℂ))
  have hn :
      (g 0 0 * u * star (g 1 0 * u) + g 0 1 * u * star (g 1 1 * u)) =
        (g 0 0 * star (g 1 0) + g 0 1 * star (g 1 1)) * (‖(u : ℂ)‖ ^ 2 : ℝ) := by
    rw [← hu]
    simp only [star_mul]
    ring
  rw [sourceArchGramShift, sourceArchBottomNorm_scalar]
  simp only [sourceKPMatrix_right_scalar_entry]
  rw [hn, Complex.ofReal_mul]
  exact mul_div_mul_right _ _ (Complex.ofReal_ne_zero.mpr
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr u.ne_zero)))

theorem sourceArchGramCoordinates_scalar (g : GL (Fin 2) ℂ) (u : ℂˣ) :
    sourceArchGramCoordinates (g * GeneralLinearGroup.scalar (Fin 2) u) =
      sourceArchGramCoordinates g := by
  apply Prod.ext
  · exact sourceArchGramShift_scalar g u
  · exact Subtype.ext (sourceArchHeight_scalar g u)

theorem sourceArchGram_unitary (g : GL (Fin 2) ℂ) (k : Matrix.unitaryGroup (Fin 2) ℂ) :
    ((g * sourceArchUnitaryGL k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      star ((g * sourceArchUnitaryGL k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    (g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  change ((g : Matrix (Fin 2) (Fin 2) ℂ) * k.val) *
    star ((g : Matrix (Fin 2) (Fin 2) ℂ) * k.val) = _
  rw [star_mul, mul_assoc, ← mul_assoc k.val, k.property.2, one_mul]

theorem sourceArchGramShift_unitary (g : GL (Fin 2) ℂ) (k : Matrix.unitaryGroup (Fin 2) ℂ) :
    sourceArchGramShift (g * sourceArchUnitaryGL k) = sourceArchGramShift g := by
  rw [sourceArchGramShift_eq_gram, sourceArchGram_unitary, ← sourceArchGramShift_eq_gram]

theorem sourceArchGramCoordinates_unitary (g : GL (Fin 2) ℂ)
    (k : Matrix.unitaryGroup (Fin 2) ℂ) :
    sourceArchGramCoordinates (g * sourceArchUnitaryGL k) = sourceArchGramCoordinates g := by
  apply Prod.ext
  · exact sourceArchGramShift_unitary g k
  · exact Subtype.ext (sourceArchHeight_unitary g k)

theorem sourceArchGramCoordinates_borel (b : GL (Fin 2) ℂ)
    (hb : b ∈ sourceGL2NormalizedBorel ℂ) :
    sourceArchGramCoordinates b = (b 0 1, ⟨‖(GeneralLinearGroup.det b : ℂ)‖,
      norm_pos_iff.mpr (GeneralLinearGroup.det b).ne_zero⟩) := by
  apply Prod.ext
  · simp [sourceArchGramCoordinates, sourceArchGramShift, sourceArchBottomNorm, hb.1, hb.2]
  · apply Subtype.ext
    simp [sourceArchGramCoordinates, sourceArchHeight, sourceArchBottomNorm, hb.1, hb.2]

def sourceArchUpperHalfSection (p : SourceArchUpperHalfSpace) : GL (Fin 2) ℂ :=
  (upperSection p.1 p.2.val p.2.property : GL (Fin 2) ℂ)

theorem sourceArchGramCoordinates_section (p : SourceArchUpperHalfSpace) :
    sourceArchGramCoordinates (sourceArchUpperHalfSection p) = p := by
  apply Prod.ext
  · let r : ℝ := Real.sqrt p.2.val
    have hr : r ≠ 0 := (Real.sqrt_pos.mpr p.2.property).ne'
    change ((r : ℂ) * star (0 : ℂ) +
      (p.1 / (r : ℂ)) * star ((r : ℂ)⁻¹)) /
      ((‖(0 : ℂ)‖ ^ 2 + ‖(r : ℂ)⁻¹‖ ^ 2 : ℝ) : ℂ) = p.1
    have hs : star ((r : ℂ)⁻¹) = (r : ℂ)⁻¹ := by simp
    simp only [star_zero, mul_zero, zero_add, hs, norm_zero,
      zero_pow (by decide : 2 ≠ 0), norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (show 0 ≤ r from Real.sqrt_nonneg p.2.val)]
    rw [Complex.ofReal_pow, Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.mpr hr]
  · exact Subtype.ext (sourceArchHeight_upperSection p.1 p.2.val p.2.property)

theorem sourceArchUpperHalfSection_continuous : Continuous sourceArchUpperHalfSection := by
  apply SpecialLinearGroup.continuous_toGL.comp
  apply Continuous.subtype_mk
  change Continuous (fun p : SourceArchUpperHalfSpace =>
    !![(Real.sqrt p.2.val : ℂ), p.1 / (Real.sqrt p.2.val : ℂ);
      0, (Real.sqrt p.2.val : ℂ)⁻¹])
  have hr : Continuous (fun p : SourceArchUpperHalfSpace => (Real.sqrt p.2.val : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_snd))
  have hr0 (p : SourceArchUpperHalfSpace) : (Real.sqrt p.2.val : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr p.2.property).ne'
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j
  · exact hr
  · exact continuous_fst.div hr hr0
  · exact continuous_const
  · exact hr.inv₀ hr0

end
end ArtinMatthews.SourceArchJacquet
