module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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

open scoped ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

/-- A crude determinant/trace estimate suffices for the a priori estimates;
the sharp arithmetic–geometric-mean constant is not needed. -/
theorem complex_det_le_trace_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    A.det.re ≤ A.trace.re ^ Fintype.card ι := by
  have hd : A.det.re = ∏ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    rfl
  have ht : A.trace.re = ∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum]
    rfl
  rw [hd, ht]
  calc
    ∏ i, hA.isHermitian.eigenvalues i ≤ ∏ _i : ι, ∑ j, hA.isHermitian.eigenvalues j :=
      Finset.prod_le_prod₀ (fun i _ ↦ hA.eigenvalues_nonneg i)
        (fun i _ ↦ Finset.single_le_sum (fun j _ ↦ hA.eigenvalues_nonneg j) (Finset.mem_univ i))
    _ = (∑ i, hA.isHermitian.eigenvalues i) ^ Fintype.card ι := by simp

/-- A determinant upper bound forces a uniform positive lower bound for the
trace of the positive inverse, without any bound on the original eigenvalues. -/
theorem complex_inverse_trace_lower {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B : Matrix ι ι ℂ) (hA : A.PosDef) (hB : B.PosDef) (hAB : A * B = 1)
    {M : ℝ} (hM : A.det.re ≤ M) : 1 / (M + 1) ≤ B.trace.re := by
  have ha : 0 < A.det.re := (Complex.pos_iff.mp hA.det_pos).1
  have hS : 0 < B.trace.re := (Complex.pos_iff.mp hB.trace_pos).1
  have hm : 0 < M := ha.trans_le hM
  have hdet : A.det.re * B.det.re = 1 := by
    have h := congrArg Complex.re (congrArg Matrix.det hAB)
    have hai : A.det.im = 0 := by
      rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
      rfl
    simpa only [Matrix.det_mul, Matrix.det_one, Complex.mul_re, hai, zero_mul,
      sub_zero, Complex.one_re] using h
  by_contra hnot
  have hlt : B.trace.re < 1 / (M + 1) := lt_of_not_ge hnot
  have hS1 : B.trace.re ≤ 1 := hlt.le.trans ((div_le_iff₀ (by linarith : 0 < M + 1)).mpr (by linarith))
  have hp1 (k : ℕ) : B.trace.re ^ k ≤ 1 := by
    induction k with
    | zero => simp
    | succ k hk =>
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right hk hS.le).trans (by simpa using hS1)
  have hp : B.trace.re ^ Fintype.card ι ≤ B.trace.re := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
    rw [hk, pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hp1 k) hS.le
  have hdb : B.det.re ≤ B.trace.re := (complex_det_le_trace_pow B hB.posSemidef).trans hp
  have hle : 1 ≤ M * B.trace.re := by
    calc
      1 = A.det.re * B.det.re := hdet.symm
      _ ≤ A.det.re * B.trace.re := mul_le_mul_of_nonneg_left hdb ha.le
      _ ≤ M * B.trace.re := mul_le_mul_of_nonneg_right hM hS.le
  have hlt' := (lt_div_iff₀ (by linarith : 0 < M + 1)).mp hlt
  nlinarith

end OAI.Analysis.PDE.Dirichlet
