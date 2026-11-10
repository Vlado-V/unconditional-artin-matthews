module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import OAI.Analysis.Calculus.Quaternion.Algebra
public import OAI.LinearAlgebra.Moore.Basic
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
public import OAI.LinearAlgebra.Moore.Boundary
public import OAI.LinearAlgebra.Moore.Inverse
public import OAI.LinearAlgebra.Moore.Normalize
public import OAI.LinearAlgebra.Moore.Square


set_option backward.privateInPublic true
@[expose] public section

open Set Filter
open scoped Matrix ComplexOrder Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem mooreDet_sq_eq_complexify_det_of_posSemidef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) OAI.Analysis.Calculus.Quaternion.Q) (hA : (OAI.LinearAlgebra.Moore.complexify A).PosSemidef) :
    OAI.LinearAlgebra.Moore.mooreDet n A ^ 2 = (OAI.LinearAlgebra.Moore.complexify A).det.re := by
  have hline : Continuous (fun t : ℝ ↦ A + t • (1 : Matrix (Fin n) (Fin n) OAI.Analysis.Calculus.Quaternion.Q)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hleft : Continuous (fun t : ℝ ↦ OAI.LinearAlgebra.Moore.mooreDet n (A + t • 1) ^ 2) :=
    ((OAI.LinearAlgebra.Moore.continuous_mooreDet n).comp hline).pow 2
  have hright : Continuous (fun t : ℝ ↦ (OAI.LinearAlgebra.Moore.complexify (A + t • 1)).det.re) := by
    apply Complex.continuous_re.comp
    apply Continuous.matrix_det
    simp only [OAI.LinearAlgebra.Moore.complexify_add, OAI.LinearAlgebra.Moore.complexify_real_smul, OAI.LinearAlgebra.Moore.complexify_one]
    fun_prop
  have hclosed := isClosed_eq hleft hright
  have hsub : Ioi (0 : ℝ) ⊆ {t | OAI.LinearAlgebra.Moore.mooreDet n (A + t • 1) ^ 2 = (OAI.LinearAlgebra.Moore.complexify (A + t • 1)).det.re} := by
    intro t ht
    exact OAI.LinearAlgebra.Moore.mooreDet_sq_eq_complexify_det_of_posDef _ (OAI.LinearAlgebra.Moore.complexify_add_pos_identity A hA ht)
  have hzero : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by simp
  have heq : OAI.LinearAlgebra.Moore.mooreDet n (A + (0 : ℝ) • 1) ^ 2 = (OAI.LinearAlgebra.Moore.complexify (A + (0 : ℝ) • 1)).det.re :=
    closure_minimal hsub hclosed hzero
  simpa only [zero_smul, add_zero] using heq

theorem complex_posDef_of_posSemidef_det_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (hdet : 0 < A.det.re) : A.PosDef := by
  have hd : A.det.re = ∏ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    rfl
  rw [hd] at hdet
  apply hA.isHermitian.posDef_iff_eigenvalues_pos.mpr
  intro i
  have hi : hA.isHermitian.eigenvalues i ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hdet.ne') i (Finset.mem_univ i)
  exact lt_of_le_of_ne (hA.eigenvalues_nonneg i) hi.symm

/-- A positive Moore determinant excludes every singular positive-semidefinite
boundary limit. This is used for data-uniform ellipticity. -/
theorem complexify_posDef_of_posSemidef_mooreDet_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) OAI.Analysis.Calculus.Quaternion.Q) (hA : (OAI.LinearAlgebra.Moore.complexify A).PosSemidef)
    (hdet : 0 < OAI.LinearAlgebra.Moore.mooreDet n A) : (OAI.LinearAlgebra.Moore.complexify A).PosDef := by
  apply complex_posDef_of_posSemidef_det_pos _ hA
  rw [← mooreDet_sq_eq_complexify_det_of_posSemidef A hA]
  positivity

end OAI.Analysis.PDE.Dirichlet
