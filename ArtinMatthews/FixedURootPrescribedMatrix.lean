module

public import ArtinMatthews.FixedURootBoxes
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Integer representatives of every prescribed special-linear matrix and
the literal entrywise meaning of its root-completion congruence. -/
namespace ArtinMatthews

/-- Canonical integer representatives of entries of the prescribed matrix. -/
noncomputable def fixedURootMatrixEntry {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (i j : Fin 2) : ℤ :=
  ((g₀ i j).val : ℤ)

@[simp] theorem fixedURootMatrixEntry_cast {S : ℕ} [NeZero S]
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (i j : Fin 2) :
    (fixedURootMatrixEntry g₀ i j : ZMod S) = g₀ i j := by
  simp only [fixedURootMatrixEntry,Int.cast_natCast,ZMod.natCast_zmod_val]

/-- Every prescribed matrix supplies the exact determinant-one integer
congruence required by the root-count theorem. -/
theorem fixedURootMatrixEntry_det {S : ℕ} [NeZero S]
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) :
    Int.ModEq (S : ℤ)
      (fixedURootMatrixEntry g₀ 0 0 * fixedURootMatrixEntry g₀ 1 1 -
        fixedURootMatrixEntry g₀ 0 1 * fixedURootMatrixEntry g₀ 1 0) 1 := by
  apply (ZMod.intCast_eq_intCast_iff _ _ S).mp
  simpa only [Int.cast_sub,Int.cast_mul,Int.cast_one,fixedURootMatrixEntry_cast,
    Matrix.det_fin_two] using g₀.prop

/-- Entrywise reduction of an actual integer root matrix equals the
prescribed matrix exactly when the four displayed congruences hold. -/
theorem fixedURootMatrix_modEq_iff {S : ℕ} [NeZero S]
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (u c v d : ℤ) :
    ((!![(u : ZMod S), (c : ZMod S); (v : ZMod S), (d : ZMod S)] :
        Matrix (Fin 2) (Fin 2) (ZMod S)) = (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S))) ↔
      Int.ModEq (S : ℤ) u (fixedURootMatrixEntry g₀ 0 0) ∧
      Int.ModEq (S : ℤ) c (fixedURootMatrixEntry g₀ 0 1) ∧
      Int.ModEq (S : ℤ) v (fixedURootMatrixEntry g₀ 1 0) ∧
      Int.ModEq (S : ℤ) d (fixedURootMatrixEntry g₀ 1 1) := by
  simp only [← ZMod.intCast_eq_intCast_iff,fixedURootMatrixEntry_cast]
  constructor
  · intro h
    exact ⟨congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod S) => A 0 0) h,
      congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod S) => A 0 1) h,
      congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod S) => A 1 0) h,
      congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod S) => A 1 1) h⟩
  · rintro ⟨hu,hc,hv,hd⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simpa using (by assumption)

/-- The literal root-box set for a prescribed special-linear matrix. -/
noncomputable def fixedURootMatrixBoxPoints {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (lcU rcU lcC rcC lcV rcV : Bool) : Finset (Σ _u : ℤ, ℤ × ℤ) :=
  fixedURootBoxPoints S (fixedURootMatrixEntry g₀ 0 0) (fixedURootMatrixEntry g₀ 0 1)
    (fixedURootMatrixEntry g₀ 1 0) (fixedURootMatrixEntry g₀ 1 1)
    A B α β C D lcU rcU lcC rcC lcV rcV

end ArtinMatthews
