module

public import ArtinMatthews.SpectralCompactFormPencil
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The genuine invariant orthogonal complement of one eigenspace of a
compact symmetric operator. Its complementary pencil is invertible at the
chosen eigenparameter by the proved compact Fredholm alternative. -/
noncomputable section
open scoped InnerProductSpace
namespace ArtinMatthews

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

abbrev SpectralCompactEigenspace (T : V →L[ℂ] V) (μ : ℂ) : Submodule ℂ V :=
  Module.End.eigenspace T.toLinearMap μ

abbrev SpectralCompactEigenComplement (T : V →L[ℂ] V) (μ : ℂ) : Submodule ℂ V :=
  (SpectralCompactEigenspace T μ)ᗮ

local instance spectralCompactEigenComplement_complete (T : V →L[ℂ] V) (μ : ℂ) :
    CompleteSpace (SpectralCompactEigenComplement T μ) :=
  (Submodule.isClosed_orthogonal _).isComplete.completeSpace_coe

omit [CompleteSpace V] in
theorem spectralCompactEigenComplement_invariant (T : V →L[ℂ] V)
    (hTs : T.toLinearMap.IsSymmetric) (μ : ℂ) (u : SpectralCompactEigenComplement T μ) :
    T u.val ∈ SpectralCompactEigenComplement T μ := by
  apply ((SpectralCompactEigenspace T μ).mem_orthogonal _).mpr
  intro y hy
  have he : T y=μ • y := Module.End.mem_eigenspace_iff.mp hy
  have hz := ((SpectralCompactEigenspace T μ).mem_orthogonal _).mp u.property y hy
  calc
    inner ℂ y (T u.val)=inner ℂ (T y) u.val := (hTs y u.val).symm
    _=0 := by rw [he,inner_smul_left,hz,mul_zero]

def spectralCompactEigenComplementCompression (T : V →L[ℂ] V) (μ : ℂ) :
    SpectralCompactEigenComplement T μ →L[ℂ] SpectralCompactEigenComplement T μ :=
  (SpectralCompactEigenComplement T μ).orthogonalProjectionOnto.comp
    (T.comp (SpectralCompactEigenComplement T μ).subtypeL)

theorem spectralCompactEigenComplementCompression_val (T : V →L[ℂ] V)
    (hTs : T.toLinearMap.IsSymmetric) (μ : ℂ) (u : SpectralCompactEigenComplement T μ) :
    (spectralCompactEigenComplementCompression T μ u).val=T u.val := by
  let W := SpectralCompactEigenComplement T μ
  let v : W := ⟨T u.val,spectralCompactEigenComplement_invariant T hTs μ u⟩
  exact congrArg Subtype.val (W.orthogonalProjectionOnto_mem_subspace_eq_self v)

theorem spectralCompactEigenComplementCompression_compact (T : V →L[ℂ] V)
    (hT : IsCompactOperator T) (μ : ℂ) : IsCompactOperator (spectralCompactEigenComplementCompression T μ) :=
  (hT.comp_clm (SpectralCompactEigenComplement T μ).subtypeL).clm_comp
    (SpectralCompactEigenComplement T μ).orthogonalProjectionOnto

theorem spectralCompactEigenComplementPencil_isUnit (T : V →L[ℂ] V)
    (hT : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) (z : ℂ) (hz : z+1≠0) :
    IsUnit (spectralCompactFormPencil (spectralCompactEigenComplementCompression T ((z+1)⁻¹)) z) := by
  let μ : ℂ := (z+1)⁻¹
  let W := SpectralCompactEigenComplement T μ
  apply (spectralCompactFormPencil_isUnit_iff _ (spectralCompactEigenComplementCompression_compact T hT μ) z).mpr
  intro u hu
  have hv := congrArg (fun v : W => v.val) hu
  change u.val-(z+1) • (spectralCompactEigenComplementCompression T μ u).val=0 at hv
  rw [spectralCompactEigenComplementCompression_val T hTs] at hv
  have he : T u.val=μ • u.val := calc
    _=μ • ((z+1) • T u.val) := by rw [smul_smul,show μ*(z+1)=1 from inv_mul_cancel₀ hz,one_smul]
    _=_ := congrArg (fun x : V => μ • x) (sub_eq_zero.mp hv).symm
  have hm : u.val ∈ SpectralCompactEigenspace T μ := Module.End.mem_eigenspace_iff.mpr he
  have horth := ((SpectralCompactEigenspace T μ).mem_orthogonal _).mp u.property u.val hm
  exact Subtype.ext (inner_self_eq_zero.mp horth)

end
end ArtinMatthews
