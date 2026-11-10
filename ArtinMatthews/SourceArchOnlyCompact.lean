module

public import ArtinMatthews.SourceKPAdelicMatrixLift
public import ArtinMatthews.SourceKPAdelicCompactSection
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

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceArchOnlyGL : GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) 𝔸[K] where
  toFun g := (sourceKPGL2ProductEquiv K).symm (g,1)
  map_one' := (sourceKPGL2ProductEquiv K).injective (by rw [MulEquiv.apply_symm_apply, map_one]; rfl)
  map_mul' g h := (sourceKPGL2ProductEquiv K).injective (by
    rw [MulEquiv.apply_symm_apply, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact Prod.ext rfl (one_mul 1).symm)

theorem sourceArchOnlyGL_product (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceKPGL2ProductEquiv K (sourceArchOnlyGL K g) = (g,1) :=
  (sourceKPGL2ProductEquiv K).apply_symm_apply _

theorem sourceArchOnlyGL_finite (g : GL (Fin 2) (InfiniteAdeleRing K))
    (P : HeightOneSpectrum (𝓞 K)) : sourceKPAdelicBaseFiniteAt K P (sourceArchOnlyGL K g) = 1 := by
  change sourceKPAdeleMatrixAt K P ((sourceKPGL2ProductEquiv K (sourceArchOnlyGL K g)).2) = 1
  rw [sourceArchOnlyGL_product]
  exact map_one _

theorem sourceArchOnlyGL_complex (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K) :
    sourceKPAdelicBaseComplexAt K hζ v (sourceArchOnlyGL K g) =
      sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v) := by
  change sourceKPArchMatrixComplexEquiv K hζ v
    (sourceArchGLPiEquiv K ((sourceKPGL2ProductEquiv K (sourceArchOnlyGL K g)).1) v) = _
  rw [sourceArchOnlyGL_product]

theorem sourceArchOnlyGL_deepCompact (g : GL (Fin 2) (InfiniteAdeleRing K))
    (hg : ∀ v : InfinitePlace K,
      sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v) ∈ sourceArchUnitaryGL.range) :
    sourceArchOnlyGL K g ∈ sourceKPAdelicDeepCompactMatrix K hζ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro P
    rw [sourceArchOnlyGL_finite]
    exact sourceKPIntegralMatrix_one _
  · intro v
    rw [sourceArchOnlyGL_complex]
    exact hg v
  · intro P _
    rw [sourceArchOnlyGL_finite]
    exact (sourceKPDeepLocalBase K P).range.one_mem

theorem sourceArchOnlyGL_lift (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceKPAdelicMatrixLift K hζ (sourceArchOnlyGL K g) = (ProjGenLinGroup.mk g,1) := by
  unfold sourceKPAdelicMatrixLift
  rw [sourceArchOnlyGL_product]
  apply Prod.ext
  · rfl
  · change sourceKPFiniteAdeleProjectiveMk K hζ 1 = 1
    exact map_one _

def sourceArchOnlyCompact (g : GL (Fin 2) (InfiniteAdeleRing K))
    (hg : ∀ v : InfinitePlace K,
      sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v) ∈ sourceArchUnitaryGL.range) :
    sourceKPAdelicDeepCompact K hζ :=
  ⟨(ProjGenLinGroup.mk g,1),
    ⟨⟨sourceArchOnlyGL K g, sourceArchOnlyGL_deepCompact K hζ g hg⟩,
      (sourceKPAdelicMatrixLift_deepCompact K hζ _).symm.trans (sourceArchOnlyGL_lift K hζ g)⟩⟩

theorem sourceArchOnlyCompact_val (g : GL (Fin 2) (InfiniteAdeleRing K))
    (hg : ∀ v : InfinitePlace K,
      sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v) ∈ sourceArchUnitaryGL.range) :
    (sourceArchOnlyCompact K hζ g hg).val = (ProjGenLinGroup.mk g,1) := rfl

theorem sourceArchCompactScalar_right (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) (InfiniteAdeleRing K))
    (hg : ∀ v : InfinitePlace K,
      sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v) ∈ sourceArchUnitaryGL.range) :
    sourceKPAdelicCompactScalar K hζ s (q*(ProjGenLinGroup.mk g,1)) =
      sourceKPAdelicCompactScalar K hζ s q := by
  have h := congrArg (fun f : SourceKPAdelicPrincipalSeries K hζ s => (f.val q).val 1)
    (sourceKPAdelicCompactSection_right K hζ s (sourceArchOnlyCompact K hζ g hg))
  exact h

theorem sourceArchIwasawaCompact_mem (g : GL (Fin 2) (InfiniteAdeleRing K))
    (v : InfinitePlace K) : sourceKPArchMatrixComplexEquiv K hζ v
      (sourceArchGLPiEquiv K (sourceKPArchIwasawaCompact K hζ g) v) ∈ sourceArchUnitaryGL.range := by
  rw [sourceKPArchIwasawaCompact_at]
  exact ⟨sourceArchIwasawaUnitary _, rfl⟩

end
end ArtinMatthews
