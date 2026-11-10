module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import OAI.LinearAlgebra.Moore.Derivative
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import OAI.LinearAlgebra.Moore.Inverse
public import OAI.LinearAlgebra.Moore.Monotone
public import OAI.LinearAlgebra.Moore.Normalize
public import OAI.LinearAlgebra.Moore.Positive


set_option backward.privateInPublic true
@[expose] public section

/-! Nonnegativity at singular positive semidefinite matrices, obtained by
positive regularization and continuity of the actual determinant polynomial. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix Set Filter
open scoped MatrixOrder ComplexOrder Topology

theorem complexify_add_pos_identity {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosSemidef) {t : ℝ} (ht : 0 < t) :
    (complexify (A + t • 1)).PosDef := by
  rw [complexify_add, complexify_real_smul, complexify_one]
  exact Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul ht)

theorem mooreDet_nonneg_of_complexify_posSemidef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosSemidef) : 0 ≤ mooreDet n A := by
  have hc := (hasDerivAt_mooreDet_affine A 1 0).continuousAt
  have ht : Tendsto (fun t : ℝ ↦ mooreDet n (A + t • 1)) (𝓝[>] 0)
      (𝓝 (mooreDet n (A + (0 : ℝ) • 1))) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 ≤ mooreDet n (A + t • 1) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (mooreDet_pos_of_complexify_posDef _ (complexify_add_pos_identity A hA ht)).le
  simpa only [zero_smul, add_zero] using ge_of_tendsto ht hpos

theorem continuous_skewComplexify_entry {n : ℕ} (i j : Fin n × Fin 2) :
    Continuous (fun A : Matrix (Fin n) (Fin n) (Quaternion ℝ) ↦ skewComplexify A i j) := by
  exact (skewQuaternionEntryCLM i.2 j.2).continuous.comp
    ((continuous_apply j.1).comp (continuous_apply i.1))

theorem continuous_mooreDet (n : ℕ) : Continuous (mooreDet n) := by
  unfold mooreDet pfaffian
  apply Complex.continuous_re.comp
  apply continuous_const.mul
  apply continuous_finsetSum
  intro σ _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro i _
  exact continuous_skewComplexify_entry (σ (i, 0)) (σ (i, 1))

/-- Continuity of the cofactor differential is proved from its finite polynomial
formula, including at singular matrices. -/
theorem continuous_mooreDifferential (n : ℕ) :
    Continuous (fun p : Matrix (Fin n) (Fin n) (Quaternion ℝ) ×
      Matrix (Fin n) (Fin n) (Quaternion ℝ) ↦ mooreDifferential n p.1 p.2) := by
  unfold mooreDifferential pfaffianDifferential
  apply Complex.continuous_re.comp
  apply continuous_const.mul
  apply continuous_finsetSum
  intro σ _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul
  · apply continuous_finsetProd
    intro j _
    exact (continuous_skewComplexify_entry (σ (j, 0)) (σ (j, 1))).comp continuous_fst
  · exact (continuous_skewComplexify_entry (σ (i, 0)) (σ (i, 1))).comp continuous_snd

/-- Even at a singular positive semidefinite background, the Moore cofactor
functional is nonnegative on every positive semidefinite direction. -/
theorem mooreDifferential_nonneg_of_posSemidef {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosSemidef) (hD : (complexify D).PosSemidef) :
    0 ≤ mooreDifferential n A D := by
  have hi : Continuous (fun t : ℝ ↦
      (A + t • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)), D)) :=
    (continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const
  have hc : Continuous (fun t : ℝ ↦ mooreDifferential n (A + t • 1) D) :=
    (continuous_mooreDifferential n).comp
      (f := fun t : ℝ ↦ (A + t • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)), D)) hi
  have ht : Tendsto (fun t : ℝ ↦ mooreDifferential n (A + t • 1) D) (𝓝[>] 0)
      (𝓝 (mooreDifferential n (A + (0 : ℝ) • 1) D)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 ≤ mooreDifferential n (A + t • 1) D := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mooreDifferential_nonneg_of_posDef _ _ (complexify_add_pos_identity A hA ht) hD
  simpa only [zero_smul, add_zero] using ge_of_tendsto ht hpos

end OAI.LinearAlgebra.Moore
