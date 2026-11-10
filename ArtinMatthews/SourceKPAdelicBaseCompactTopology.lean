module

public import ArtinMatthews.SourceAdelicIwasawa
public import ArtinMatthews.SourceKPFiniteMatrixTopology
public import ArtinMatthews.SourceArchCompactUnitary
public import ArtinMatthews.SourceKPAdelicCompactIntersection
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
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Compactness of the actual full adelic base matrix subgroup. -/

namespace ArtinMatthews
open NumberField Topology Matrix SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

theorem sourceKPGL2ProductEquiv_symm_continuous :
    Continuous (sourceKPGL2ProductEquiv K).symm := by
  apply Continuous.of_coeHom_comp (f := (sourceKPGL2ProductEquiv K).symm.toMonoidHom)
  change Continuous (fun p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) 𝔸ᶠ[K] =>
    ((sourceKPGL2ProductEquiv K).symm p : Matrix (Fin 2) (Fin 2) 𝔸[K]))
  apply continuous_matrix
  intro i j
  have he (p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) 𝔸ᶠ[K]) :
      (sourceKPGL2ProductEquiv K).symm p i j = (p.1 i j, p.2 i j) := by
    have hp := (sourceKPGL2ProductEquiv K).apply_symm_apply p
    exact Prod.ext (congrArg (fun q => q.1 i j) hp) (congrArg (fun q => q.2 i j) hp)
  simp_rw [he]
  exact ((Units.continuous_val.matrix_elem i j).comp continuous_fst).prodMk
    ((Units.continuous_val.matrix_elem i j).comp continuous_snd)

omit [NumberField K] in
theorem sourceKPArchGLPiEquiv_symm_continuous :
    Continuous (sourceArchGLPiEquiv K).symm := by
  apply Continuous.of_coeHom_comp (f := (sourceArchGLPiEquiv K).symm.toMonoidHom)
  change Continuous (fun p : ∀ v : InfinitePlace K, GL (Fin 2) v.Completion =>
    ((sourceArchGLPiEquiv K).symm p : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)))
  apply continuous_matrix
  intro i j
  apply continuous_pi
  intro v
  have he (p : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) :
      (sourceArchGLPiEquiv K).symm p i j v = p v i j :=
    congrArg (fun q => q v i j) ((sourceArchGLPiEquiv K).apply_symm_apply p)
  simp_rw [he]
  exact (Units.continuous_val.matrix_elem i j).comp (continuous_apply v)

theorem sourceKPArchUnitaryGL_continuous : Continuous sourceArchUnitaryGL := by
  apply Continuous.of_coeHom_comp
  exact continuous_subtype_val

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchMatrixComplexEquiv_symm_continuous (v : InfinitePlace K) :
    Continuous (sourceKPArchMatrixComplexEquiv K hζ v).symm := by
  have hn (x : ℂ) : ‖(sourceKPArchComplexEquiv K hζ v).symm x‖ = ‖x‖ := by
    simpa only [RingEquiv.apply_symm_apply] using
      (sourceKPArchComplexEquiv_norm K hζ v ((sourceKPArchComplexEquiv K hζ v).symm x)).symm
  have hc : Continuous (sourceKPArchComplexEquiv K hζ v).symm :=
    (AddMonoidHomClass.isometry_of_norm (sourceKPArchComplexEquiv K hζ v).symm hn).continuous
  change Continuous (GeneralLinearGroup.map (sourceKPArchComplexEquiv K hζ v).symm.toRingHom)
  exact hc.generalLinearGroup_map

def sourceKPAdelicBaseCompactParam
    (p : (InfinitePlace K → Matrix.unitaryGroup (Fin 2) ℂ) × sourceKPFiniteIntegralMatrixGroup K) :
    GL (Fin 2) 𝔸[K] :=
  (sourceKPGL2ProductEquiv K).symm
    ((sourceArchGLPiEquiv K).symm (fun v => (sourceKPArchMatrixComplexEquiv K hζ v).symm
      (sourceArchUnitaryGL (p.1 v))), p.2.val)

theorem sourceKPAdelicBaseCompactParam_continuous :
    Continuous (sourceKPAdelicBaseCompactParam K hζ) := by
  apply (sourceKPGL2ProductEquiv_symm_continuous K).comp
  apply Continuous.prodMk ?_ (continuous_subtype_val.comp continuous_snd)
  apply (sourceKPArchGLPiEquiv_symm_continuous K).comp
  apply continuous_pi
  intro v
  exact (sourceKPArchMatrixComplexEquiv_symm_continuous K hζ v).comp
    (sourceKPArchUnitaryGL_continuous.comp ((continuous_apply v).comp continuous_fst))

theorem sourceKPAdelicBaseCompactParam_range :
    Set.range (sourceKPAdelicBaseCompactParam K hζ) =
      (SourceKPAdelicBaseCompactMatrix K hζ : Set (GL (Fin 2) 𝔸[K])) := by
  classical
  ext g
  constructor
  · rintro ⟨p, rfl⟩
    constructor
    · intro P
      change SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPAdeleMatrixAt K P
        ((sourceKPGL2ProductEquiv K (sourceKPAdelicBaseCompactParam K hζ p)).2))
      rw [sourceKPAdelicBaseCompactParam, MulEquiv.apply_symm_apply]
      exact (sourceKPFiniteIntegralMatrixGroup_mem K p.2.val).mp p.2.property P
    · intro v
      change sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K
        ((sourceKPGL2ProductEquiv K (sourceKPAdelicBaseCompactParam K hζ p)).1) v) ∈ _
      rw [sourceKPAdelicBaseCompactParam, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply]
      exact ⟨p.1 v, rfl⟩
  · intro hg
    have hfin : (sourceKPGL2ProductEquiv K g).2 ∈ sourceKPFiniteIntegralMatrixGroup K := by
      apply (sourceKPFiniteIntegralMatrixGroup_mem K _).mpr
      intro P
      exact hg.1 P
    choose k hk using hg.2
    refine ⟨(k, ⟨(sourceKPGL2ProductEquiv K g).2, hfin⟩), ?_⟩
    apply (sourceKPGL2ProductEquiv K).injective
    rw [sourceKPAdelicBaseCompactParam, MulEquiv.apply_symm_apply]
    apply Prod.ext
    · apply (sourceArchGLPiEquiv K).injective
      rw [MulEquiv.apply_symm_apply]
      funext v
      apply (sourceKPArchMatrixComplexEquiv K hζ v).injective
      rw [MulEquiv.apply_symm_apply]
      exact hk v
    · rfl

theorem SourceKPAdelicBaseCompactMatrix_isCompact :
    IsCompact (SourceKPAdelicBaseCompactMatrix K hζ : Set (GL (Fin 2) 𝔸[K])) := by
  let : CompactSpace (Matrix.unitaryGroup (Fin 2) ℂ) :=
    isCompact_iff_compactSpace.mp sourceArchUnitary_isCompact
  let : CompactSpace (sourceKPFiniteIntegralMatrixGroup K) :=
    isCompact_iff_compactSpace.mp (sourceKPFiniteIntegralMatrixGroup_isCompact K)
  rw [← sourceKPAdelicBaseCompactParam_range K hζ]
  exact isCompact_range (sourceKPAdelicBaseCompactParam_continuous K hζ)

end
end ArtinMatthews
