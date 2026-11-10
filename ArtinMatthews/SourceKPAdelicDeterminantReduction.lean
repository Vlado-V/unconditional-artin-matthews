module

public import ArtinMatthews.SourceKPAdelicHeight
public import ArtinMatthews.SourceKPIdeleNormFlow
public import ArtinMatthews.SourceKPIdeleNormOneCompact
public import ArtinMatthews.SourceKPAdelicBorelBand
public import ArtinMatthews.SourceKPAdelicHeightFactor
public import ArtinMatthews.SourceKPAdelicSectionBound
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

/-! Central norm scaling and rational determinant reduction place the
remaining determinant in an actual compact set, leaving an SL₂ factor. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicDeterminantScale (v₀ : InfinitePlace K) (g : GL (Fin 2) 𝔸[K]) :
    IdeleGroup (𝓞 K) K :=
  sourceKPIdeleNormFlow K hζ v₀
    (-Real.log (sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det g))/2)

theorem sourceKPAdelicDeterminantScale_norm_one (v₀ : InfinitePlace K)
    (g : GL (Fin 2) 𝔸[K]) :
    sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det
      (g * GeneralLinearGroup.scalar (Fin 2) (sourceKPAdelicDeterminantScale K hζ v₀ g))) = 1 := by
  unfold sourceKPAdelicDeterminantScale
  rw [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, map_mul, map_pow,
    sourceKPIdeleNormFlow_norm, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (2 : ℝ) * (-Real.log (sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det g))/2) =
      -Real.log (sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det g)) := by ring
  rw [he, Real.exp_neg, Real.exp_log (sourceKPIdeleAbsoluteNorm_pos K _),
    mul_inv_cancel₀ (sourceKPIdeleAbsoluteNorm_pos K _).ne']

theorem sourceKPAdelicDeterminantScale_height (v₀ : InfinitePlace K)
    (g : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicHeight K hζ
      (g * GeneralLinearGroup.scalar (Fin 2) (sourceKPAdelicDeterminantScale K hζ v₀ g)) =
        sourceKPAdelicHeight K hζ g := by
  apply (sourceKPAdelicHeight_projective K hζ g _ ?_).symm
  exact ProjGenLinGroup.mk_eq_mk_iff.mpr ⟨sourceKPAdelicDeterminantScale K hζ v₀ g,rfl⟩

def sourceKPAdelicDeterminantCompact : Set (GL (Fin 2) 𝔸[K]) :=
  (sourceKPDiagonalHom 𝔸[K]) '' sourceKPIdeleNormOneCompact K

theorem sourceKPAdelicDeterminantCompact_isCompact :
    IsCompact (sourceKPAdelicDeterminantCompact K) :=
  (sourceKPIdeleNormOneCompact_isCompact K).image (sourceKPAdelicDiagonalMatrix_continuous K)

theorem sourceKPAdelicDeterminant_reduction (v₀ : InfinitePlace K)
    (g : GL (Fin 2) 𝔸[K]) :
    ∃ (q : Kˣ) (d : IdeleGroup (𝓞 K) K) (h : GL (Fin 2) 𝔸[K]),
      d ∈ sourceKPIdeleNormOneCompact K ∧ GeneralLinearGroup.det h = 1 ∧
      GeneralLinearGroup.map (algebraMap K 𝔸[K]) (sourceKPDiagonalHom K q) *
        (g * GeneralLinearGroup.scalar (Fin 2) (sourceKPAdelicDeterminantScale K hζ v₀ g)) =
          h * sourceKPDiagonalHom 𝔸[K] d := by
  let g₀ := g * GeneralLinearGroup.scalar (Fin 2) (sourceKPAdelicDeterminantScale K hζ v₀ g)
  obtain ⟨q,hq⟩ := sourceKPIdeleNormOneCompact_representative K
    (GeneralLinearGroup.det g₀) (sourceKPAdelicDeterminantScale_norm_one K hζ v₀ g)
  let p := IdeleGroup.unitEmbedding (𝓞 K) K q
  let d := GeneralLinearGroup.det g₀ * p
  let g₁ := GeneralLinearGroup.map (algebraMap K 𝔸[K]) (sourceKPDiagonalHom K q) * g₀
  have hdiag (a : IdeleGroup (𝓞 K) K) : GeneralLinearGroup.det (sourceKPDiagonalHom 𝔸[K] a) = a := by
    simpa only [sourceKPUpperMatrix_zero, one_mul] using sourceKPUpperDiagonal_det (0 : 𝔸[K]) a
  have hg₁ : GeneralLinearGroup.det g₁ = d := by
    change GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap K 𝔸[K]) (sourceKPDiagonalHom K q) * g₀) = _
    rw [sourceKPDiagonalHom_map, map_mul, hdiag]
    exact mul_comm _ _
  let h := g₁ * sourceKPDiagonalHom 𝔸[K] d⁻¹
  have hh : GeneralLinearGroup.det h = 1 := by
    change GeneralLinearGroup.det (g₁ * sourceKPDiagonalHom 𝔸[K] d⁻¹) = 1
    rw [map_mul, hg₁, hdiag, mul_inv_cancel]
  refine ⟨q,d,h,hq,hh, ?_⟩
  change g₁ = (g₁ * sourceKPDiagonalHom 𝔸[K] d⁻¹) * sourceKPDiagonalHom 𝔸[K] d
  rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

theorem sourceKPAdelicSL2_compact_determinant_reduction (v₀ : InfinitePlace K)
    (g : GL (Fin 2) 𝔸[K]) :
    ∃ (q : Kˣ) (d : IdeleGroup (𝓞 K) K) (h : SL(2, 𝔸[K])),
      d ∈ sourceKPIdeleNormOneCompact K ∧
      GeneralLinearGroup.map (algebraMap K 𝔸[K]) (sourceKPDiagonalHom K q) *
        (g * GeneralLinearGroup.scalar (Fin 2) (sourceKPAdelicDeterminantScale K hζ v₀ g)) =
          h.toGL * sourceKPDiagonalHom 𝔸[K] d := by
  obtain ⟨q,d,h,hd,hh,he⟩ := sourceKPAdelicDeterminant_reduction K hζ v₀ g
  have hdet : Matrix.det (h : Matrix (Fin 2) (Fin 2) 𝔸[K]) = 1 := congrArg Units.val hh
  let h₀ : SL(2, 𝔸[K]) := ⟨(h : Matrix (Fin 2) (Fin 2) 𝔸[K]),hdet⟩
  have hto : h₀.toGL = h := by
    apply Units.ext
    rfl
  exact ⟨q,d,h₀,hd,hto.symm ▸ he⟩

end
end ArtinMatthews
