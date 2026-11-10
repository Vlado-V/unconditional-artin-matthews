module

public import ArtinMatthews.SourceKPArchGramProduct
public import ArtinMatthews.SourceArchSphericalProductCasimir
public import ArtinMatthews.SourceAdelicHeightFibers
public import ArtinMatthews.SourceKPAdelicBaseCompactTopology
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

/-! The full product chart has continuous actual adelic matrix
representatives, with every finite coordinate unchanged. -/

namespace ArtinMatthews
open NumberField Matrix OAI.CubicEisenstein SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

abbrev SourceKPProductUpper :=
  {p : InfinitePlace K → EuclideanSpatial // ∀ v, 0 < p v 2}

def sourceKPProductUpperCoordinates (p : SourceKPProductUpper K) :
    SourceKPArchUpperHalfSpace K :=
  fun v => (((p.val v 0 : ℂ)+(p.val v 1 : ℂ)*Complex.I),⟨p.val v 2,p.property v⟩)

omit [NumberField K] in
theorem sourceKPProductUpperCoordinates_continuous :
    Continuous (sourceKPProductUpperCoordinates K) := by
  apply continuous_pi
  intro v
  have hv : Continuous (fun p : SourceKPProductUpper K => p.val v) :=
    (continuous_apply v).comp continuous_subtype_val
  have hzero : Continuous (fun p : SourceKPProductUpper K => p.val v 0) :=
    (EuclideanSpace.proj 0).continuous.comp hv
  have hone : Continuous (fun p : SourceKPProductUpper K => p.val v 1) :=
    (EuclideanSpace.proj 1).continuous.comp hv
  have htwo : Continuous (fun p : SourceKPProductUpper K => p.val v 2) :=
    (EuclideanSpace.proj 2).continuous.comp hv
  exact ((Complex.continuous_ofReal.comp hzero).add
    ((Complex.continuous_ofReal.comp hone).mul_const Complex.I)).prodMk
      (htwo.subtype_mk (fun p => p.property v))

def sourceKPProductUpperSection (p : SourceKPProductUpper K) :
    GL (Fin 2) (InfiniteAdeleRing K) :=
  sourceKPArchUpperHalfSection K hζ (sourceKPProductUpperCoordinates K p)

theorem sourceKPProductUpperSection_eq (p : SourceKPProductUpper K) :
    sourceKPProductUpperSection K hζ p = sourceArchUpperHalfspaceMatrix K hζ p.val p.property := rfl

theorem sourceKPProductUpperSection_continuous :
    Continuous (sourceKPProductUpperSection K hζ) :=
  (sourceKPArchUpperHalfSection_continuous K hζ).comp
    (sourceKPProductUpperCoordinates_continuous K)

def sourceKPAdelicProductUpperMatrix (g : GL (Fin 2) 𝔸[K])
    (p : SourceKPProductUpper K) : GL (Fin 2) 𝔸[K] :=
  g*(sourceKPGL2ProductEquiv K).symm (sourceKPProductUpperSection K hζ p,1)

theorem sourceKPAdelicProductUpperMatrix_continuous (g : GL (Fin 2) 𝔸[K]) :
    Continuous (sourceKPAdelicProductUpperMatrix K hζ g) :=
  continuous_const.mul ((sourceKPGL2ProductEquiv_symm_continuous K).comp
    ((sourceKPProductUpperSection_continuous K hζ).prodMk continuous_const))

theorem sourceKPAdelicProductUpperMatrix_projection (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K]) (hg : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g)
    (p : SourceKPProductUpper K) :
    sourceKPAdelicProjectiveProjection K hζ
      (q*(ProjGenLinGroup.mk (sourceKPProductUpperSection K hζ p),1)) =
        ProjGenLinGroup.mk (sourceKPAdelicProductUpperMatrix K hζ g p) := by
  rw [map_mul,hg,sourceKPAdelicProductUpperMatrix,map_mul]
  congr 1
  apply (sourceKPAdelicProjectiveProductEquiv K).injective
  rw [sourceKPAdelicProjectiveProjection_product,sourceKPAdelicProjectiveProductEquiv_mk,
    MulEquiv.apply_symm_apply]
  change (ProjGenLinGroup.mk (sourceKPProductUpperSection K hζ p),
    sourceKPFiniteAdeleProjectiveProjection K hζ 1) =
      (ProjGenLinGroup.mk (sourceKPProductUpperSection K hζ p),ProjGenLinGroup.mk 1)
  rw [map_one,map_one]

end
end ArtinMatthews
