module

public import ArtinMatthews.SourceKPFiniteMatrixTopology
public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceKPAdelicMatrixLift
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

/-! Finite matrix orbit constancy of the actual full adelic compact section. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology Matrix SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPFiniteMatrixEmbedding : GL (Fin 2) 𝔸ᶠ[K] →* GL (Fin 2) 𝔸[K] :=
  (sourceKPGL2ProductEquiv K).symm.toMonoidHom.comp
    ((1 : GL (Fin 2) 𝔸ᶠ[K] →* GL (Fin 2) (InfiniteAdeleRing K)).prod (MonoidHom.id _))

lemma sourceKPFiniteMatrixEmbedding_product (g : GL (Fin 2) 𝔸ᶠ[K]) :
    sourceKPGL2ProductEquiv K (sourceKPFiniteMatrixEmbedding K g) = (1, g) :=
  (sourceKPGL2ProductEquiv K).apply_symm_apply (1, g)

lemma sourceKPFiniteMatrixEmbedding_apply (g : GL (Fin 2) 𝔸ᶠ[K]) (i j : Fin 2) :
    sourceKPFiniteMatrixEmbedding K g i j = ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, g i j) := by
  apply Prod.ext
  · exact congrArg (fun a : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) 𝔸ᶠ[K] => a.1 i j)
      (sourceKPFiniteMatrixEmbedding_product K g)
  · exact congrArg (fun a : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) 𝔸ᶠ[K] => a.2 i j)
      (sourceKPFiniteMatrixEmbedding_product K g)

lemma sourceKPFiniteMatrixEmbedding_continuous : Continuous (sourceKPFiniteMatrixEmbedding K) := by
  apply Continuous.of_coeHom_comp
  change Continuous (fun g : GL (Fin 2) 𝔸ᶠ[K] =>
    (sourceKPFiniteMatrixEmbedding K g : Matrix (Fin 2) (Fin 2) 𝔸[K]))
  apply continuous_matrix
  intro i j
  simp_rw [sourceKPFiniteMatrixEmbedding_apply]
  exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)

lemma sourceKPFiniteMatrixEmbedding_finiteAt (g : GL (Fin 2) 𝔸ᶠ[K]) (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdelicBaseFiniteAt K P (sourceKPFiniteMatrixEmbedding K g) = sourceKPAdeleMatrixAt K P g := by
  change sourceKPAdeleMatrixAt K P ((sourceKPGL2ProductEquiv K (sourceKPFiniteMatrixEmbedding K g)).2) = _
  rw [sourceKPFiniteMatrixEmbedding_product]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

lemma sourceKPFiniteMatrixEmbedding_complexAt (g : GL (Fin 2) 𝔸ᶠ[K]) (v : InfinitePlace K) :
    sourceKPAdelicBaseComplexAt K hζ v (sourceKPFiniteMatrixEmbedding K g) = 1 := by
  change sourceKPArchMatrixComplexEquiv K hζ v
    (sourceArchGLPiEquiv K ((sourceKPGL2ProductEquiv K (sourceKPFiniteMatrixEmbedding K g)).1) v) = 1
  rw [sourceKPFiniteMatrixEmbedding_product]
  simp only [map_one, Pi.one_apply]

lemma sourceKPFiniteMatrixEmbedding_mem_deepCompact (g : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPFiniteMatrixEmbedding K g.val ∈ sourceKPAdelicDeepCompactMatrix K hζ := by
  have hg := (sourceKPFiniteDeepMatrixGroup_mem K g.val).mp g.property
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro P
    rw [sourceKPFiniteMatrixEmbedding_finiteAt]
    exact hg.1 P
  · intro v
    rw [sourceKPFiniteMatrixEmbedding_complexAt]
    exact sourceArchUnitaryGL.range.one_mem
  · intro P hP
    rw [sourceKPFiniteMatrixEmbedding_finiteAt]
    exact hg.2 P hP

def sourceKPFiniteDeepIntoAdelic :
    sourceKPFiniteDeepMatrixGroup K →* sourceKPAdelicDeepCompactMatrix K hζ :=
  ((sourceKPFiniteMatrixEmbedding K).comp (sourceKPFiniteDeepMatrixGroup K).subtype).codRestrict
    (sourceKPAdelicDeepCompactMatrix K hζ) (sourceKPFiniteMatrixEmbedding_mem_deepCompact K hζ)

def sourceKPFiniteDeepCoverLift :
    sourceKPFiniteDeepMatrixGroup K →* SourceKPAdelicProjective K hζ :=
  (sourceKPAdelicDeepCompactLift K hζ).comp (sourceKPFiniteDeepIntoAdelic K hζ)

def sourceKPFiniteMatrixLift (g : GL (Fin 2) 𝔸ᶠ[K]) : SourceKPAdelicProjective K hζ :=
  sourceKPAdelicMatrixLift K hζ (sourceKPFiniteMatrixEmbedding K g)

lemma sourceKPFiniteDeepCoverLift_eq (g : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPFiniteDeepCoverLift K hζ g = sourceKPFiniteMatrixLift K hζ g.val :=
  (sourceKPAdelicMatrixLift_deepCompact K hζ (sourceKPFiniteDeepIntoAdelic K hζ g)).symm

lemma sourceKPFiniteDeepCoverLift_projection (g : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPAdelicProjectiveProjection K hζ (sourceKPFiniteDeepCoverLift K hζ g) =
      ProjGenLinGroup.mk (sourceKPFiniteMatrixEmbedding K g.val) := by
  rw [sourceKPFiniteDeepCoverLift_eq]
  exact sourceKPAdelicMatrixLift_projection K hζ _

theorem sourceKPAdelicCompactSection_finite_fixed (s : ℂ) (g : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPAdelicPrincipalSeriesRepresentation K hζ s (sourceKPFiniteMatrixLift K hζ g.val)
      (sourceKPAdelicCompactSection K hζ s) = sourceKPAdelicCompactSection K hζ s := by
  rw [← sourceKPFiniteDeepCoverLift_eq]
  exact sourceKPAdelicCompactSection_right K hζ s
    ⟨sourceKPFiniteDeepCoverLift K hζ g, ⟨sourceKPFiniteDeepIntoAdelic K hζ g, rfl⟩⟩

theorem sourceKPAdelicCompactSection_finite_eventually_fixed (s : ℂ) :
    ∀ᶠ g : GL (Fin 2) 𝔸ᶠ[K] in nhds 1,
      sourceKPAdelicPrincipalSeriesRepresentation K hζ s (sourceKPFiniteMatrixLift K hζ g)
        (sourceKPAdelicCompactSection K hζ s) = sourceKPAdelicCompactSection K hζ s := by
  have hU := (sourceKPFiniteDeepMatrixGroup_isOpen K).mem_nhds (sourceKPFiniteDeepMatrixGroup K).one_mem
  filter_upwards [hU] with g hg
  exact sourceKPAdelicCompactSection_finite_fixed K hζ s ⟨g, hg⟩

end
end ArtinMatthews
