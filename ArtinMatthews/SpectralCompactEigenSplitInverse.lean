module

public import ArtinMatthews.SpectralCompactEigenComplement
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact block inversion along one eigenspace and its invariant orthogonal
complement. The finite-rank singular piece is the actual orthogonal projection. -/
noncomputable section
open scoped InnerProductSpace
namespace ArtinMatthews

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

local instance spectralCompactEigenSplit_space_complete (T : V →L[ℂ] V) (μ : ℂ) :
    CompleteSpace (SpectralCompactEigenspace T μ) :=
  (ContinuousLinearMap.isClosed_eigenspace T μ).isComplete.completeSpace_coe

local instance spectralCompactEigenSplit_complement_complete (T : V →L[ℂ] V) (μ : ℂ) :
    CompleteSpace (SpectralCompactEigenComplement T μ) :=
  (Submodule.isClosed_orthogonal _).isComplete.completeSpace_coe

def spectralCompactEigenSplitInverse (T : V →L[ℂ] V) (μ z : ℂ) : V →L[ℂ] V :=
  let S := SpectralCompactEigenspace T μ
  let W := SpectralCompactEigenComplement T μ
  (1-(z+1)*μ)⁻¹ • S.starProjection+
    W.subtypeL.comp ((Ring.inverse
      (spectralCompactFormPencil (spectralCompactEigenComplementCompression T μ) z)).comp
        W.orthogonalProjectionOnto)

theorem spectralCompactEigenSplitInverse_right (T : V →L[ℂ] V)
    (hTs : T.toLinearMap.IsSymmetric) (μ z : ℂ) (hz : 1-(z+1)*μ≠0)
    (hW : IsUnit (spectralCompactFormPencil (spectralCompactEigenComplementCompression T μ) z)) :
    spectralCompactFormPencil T z*spectralCompactEigenSplitInverse T μ z=1 := by
  let S := SpectralCompactEigenspace T μ
  let W := SpectralCompactEigenComplement T μ
  let P := spectralCompactFormPencil (spectralCompactEigenComplementCompression T μ) z
  ext u
  let q : S := S.orthogonalProjectionOnto u
  let v : W := Ring.inverse P (W.orthogonalProjectionOnto u)
  have hTq : T q.val=μ • q.val := Module.End.mem_eigenspace_iff.mp q.property
  have hPq : spectralCompactFormPencil T z q.val=(1-(z+1)*μ) • q.val := by
    change q.val-(z+1) • T q.val=(1-(z+1)*μ) • q.val
    rw [hTq,smul_smul,sub_smul,one_smul]
  have hq : spectralCompactFormPencil T z ((1-(z+1)*μ)⁻¹ • q.val)=q.val := by
    rw [map_smul,hPq,smul_smul,inv_mul_cancel₀ hz,one_smul]
  have hv : spectralCompactFormPencil T z v.val=(P v).val := by
    change v.val-(z+1) • T v.val=v.val-(z+1) • (spectralCompactEigenComplementCompression T μ v).val
    rw [spectralCompactEigenComplementCompression_val T hTs]
  have hv' : P v=W.orthogonalProjectionOnto u :=
    congrArg (fun A : W →L[ℂ] W => A (W.orthogonalProjectionOnto u)) (Ring.mul_inverse_cancel P hW)
  change spectralCompactFormPencil T z ((1-(z+1)*μ)⁻¹ • q.val+v.val)=u
  rw [map_add,hq,hv,hv']
  exact S.starProjection_add_starProjection_orthogonal u

theorem spectralCompactEigenSplitInverse_eq_inverse (T : V →L[ℂ] V)
    (hTs : T.toLinearMap.IsSymmetric) (μ z : ℂ) (hz : 1-(z+1)*μ≠0)
    (hW : IsUnit (spectralCompactFormPencil (spectralCompactEigenComplementCompression T μ) z))
    (hP : IsUnit (spectralCompactFormPencil T z)) :
    spectralCompactEigenSplitInverse T μ z=Ring.inverse (spectralCompactFormPencil T z) := by
  let P := spectralCompactFormPencil T z
  calc
    _=(Ring.inverse P*P)*spectralCompactEigenSplitInverse T μ z := by
      rw [Ring.inverse_mul_cancel P hP,one_mul]
    _=_ := by
      rw [mul_assoc,spectralCompactEigenSplitInverse_right T hTs μ z hz hW,mul_one]

end
end ArtinMatthews
