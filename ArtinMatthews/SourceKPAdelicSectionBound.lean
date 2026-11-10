module

public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceKPAdelicHeight
public import ArtinMatthews.SourceKPAdelicHeightFactor
public import ArtinMatthews.SourceKPAdelicUpperProjection
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

/-! The concrete compact section is bounded by the actual adelic
Iwasawa height at every covering-group argument. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

theorem sourceKPUpperDiagonal_det {R : Type*} [CommRing R] (x : R) (a : Rˣ) :
    GeneralLinearGroup.det (sourceKPUpperMatrix R x * sourceKPDiagonalHom R a) = a := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, sourceKPUpperMatrix,
    sourceKPDiagonalHom]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCoveringBorel_matrix (b : sourceKPAdelicCoveringBorel K hζ) :
    ∃ m : GL (Fin 2) 𝔸[K], m ∈ sourceKPRingNormalizedBorel 𝔸[K] ∧
      sourceKPAdelicProjectiveProjection K hζ b.val = ProjGenLinGroup.mk m ∧
      GeneralLinearGroup.det m = sourceKPAdelicTorusIdele K hζ (sourceKPAdelicBorelTorusProjection K hζ b) := by
  obtain ⟨⟨x,t⟩,rfl⟩ := (sourceKPAdelicBorelCoordinatesEquiv K hζ).surjective b
  refine ⟨sourceKPUpperMatrix 𝔸[K] x *
    sourceKPDiagonalHom 𝔸[K] (sourceKPAdelicTorusIdele K hζ t), ?_, ?_, ?_⟩
  · exact (sourceKPRingNormalizedBorel 𝔸[K]).mul_mem
      (sourceKPRingNormalizedBorel_upper 𝔸[K] x) (sourceKPRingNormalizedBorel_diagonal 𝔸[K] _)
  · rw [sourceKPAdelicBorelCoordinatesEquiv_val, map_mul, sourceKPAdelicUpperLift_projection,
      sourceKPAdelicTorusIdele_projection, map_mul]
    rfl
  · rw [sourceKPAdelicBorelTorusProjection_coordinates, sourceKPUpperDiagonal_det]

theorem sourceKPAdelicCompactScalar_height_bound (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K]) (hp : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g) :
    ‖sourceKPAdelicCompactScalar K hζ s q‖ ≤ (sourceKPAdelicHeight K hζ g) ^ (s.re+1/2) := by
  by_cases hq : sourceCompactInducedFactorable (sourceKPAdelicCoveringBorel K hζ)
      (sourceKPAdelicDeepCompact K hζ) q
  · obtain ⟨b,k,he⟩ := hq
    obtain ⟨m,hm,hmp,hmd⟩ := sourceKPAdelicCoveringBorel_matrix K hζ b
    obtain ⟨k₀,hk₀⟩ := k.property
    have hg : ProjGenLinGroup.mk g = ProjGenLinGroup.mk (m*k₀.val) := by
      rw [← hp, he, map_mul, hmp, ← hk₀, sourceKPAdelicDeepCompactLift_projection, map_mul]
    have hh : sourceKPAdelicHeight K hζ g = sourceKPIdeleAbsoluteNorm K
        (sourceKPAdelicTorusIdele K hζ (sourceKPAdelicBorelTorusProjection K hζ b)) := by
      rw [sourceKPAdelicHeight_projective K hζ g (m*k₀.val) hg]
      rw [sourceKPAdelicHeight_factor K hζ (m*k₀.val) m k₀.val 1 hm k₀.property.1
        (by rw [map_one, mul_one]), hmd]
    rw [hh]
    exact sourceKPAdelicCompactScalar_factor_bound K hζ s q b k he
  · rw [sourceKPAdelicCompactScalar_zero K hζ s q hq, norm_zero]
    exact Real.rpow_nonneg (sourceKPAdelicHeight_pos K hζ g).le _

end
end ArtinMatthews
