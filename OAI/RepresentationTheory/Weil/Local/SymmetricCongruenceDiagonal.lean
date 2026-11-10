module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import OAI.RepresentationTheory.Weil.Local.SiegelGaussian


set_option backward.privateInPublic true
@[expose] public section

/-! # Symmetric Congruence Diagonal -/

namespace OAI.RepresentationTheory.Weil.Local.SymmetricCongruenceDiagonal.Construction

noncomputable section

/-! Congruence diagonalization of a nonsingular symmetric matrix over the local base field. -/

open _root_.Matrix _root_.Module

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

theorem symmetric_generalLinear_congruence_diagonal
    (M : FunctionsMetaplectic.Construction.GeneralLinear k n) (hM : M.val.IsSymm) :
    ∃ (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ),
      A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val) := by
  let : Invertible (2 : k) := invertibleOfNonzero (by norm_num)
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (K := k) (V := FunctionsMetaplectic.Construction.Position k n)
    (B := M.val.toBilin')
    (LinearMap.BilinForm.isSymm_iff.mp (Matrix.isSymm_toBilin'_iff_isSymm.mpr hM))
  let e' : Fin (finrank k (FunctionsMetaplectic.Construction.Position k n)) ≃ Fin n := finCongr (by simp [FunctionsMetaplectic.Construction.Position])
  let b : Basis (Fin n) k (FunctionsMetaplectic.Construction.Position k n) := v.reindex e'
  have hb : M.val.toBilin'.IsOrthoᵢ b := by
    intro i j hij
    change M.val.toBilin' ((v.reindex e') i) ((v.reindex e') j) = 0
    rw [Basis.reindex_apply, Basis.reindex_apply]
    exact (LinearMap.isOrthoᵢ_def.mp hv) (e'.symm i) (e'.symm j) (e'.symm.injective.ne hij)
  let e := Pi.basisFun k (Fin n)
  let A : FunctionsMetaplectic.Construction.GeneralLinear k n := {
    val := e.toMatrix b
    inv := b.toMatrix e
    val_inv := e.toMatrix_mul_toMatrix_flip b
    inv_val := b.toMatrix_mul_toMatrix_flip e }
  let d := fun i => M.val.toBilin' (b i) (b i)
  have hcol (i : Fin n) : A.val.col i = b i := by funext j; rfl
  have hdiag : A.val.transpose * M.val * A.val = diagonal d := by
    ext i j
    rw [SiegelGaussian.Construction.matrix_congruence_entry, hcol, hcol, ← Matrix.toBilin'_apply']
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq]
      rfl
    · rw [diagonal_apply_ne _ hij]
      exact hb hij
  have hAdet : A.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A.val).mp A.isUnit).ne_zero
  have hMdet : M.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M.val).mp M.isUnit).ne_zero
  have hprod : ∏ i, d i ≠ 0 := by
    rw [← det_diagonal, ← hdiag, det_mul, det_mul, det_transpose]
    exact mul_ne_zero (mul_ne_zero hAdet hMdet) hAdet
  have hd (i : Fin n) : d i ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  exact ⟨A, fun i => Units.mk0 (d i) (hd i), hdiag⟩

end

end OAI.RepresentationTheory.Weil.Local.SymmetricCongruenceDiagonal.Construction
