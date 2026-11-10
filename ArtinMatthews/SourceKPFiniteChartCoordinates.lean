module

public import ArtinMatthews.SourceKPArchActionSmooth
public import ArtinMatthews.SourceKPCompactCoreCharts
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

/-! The selected finite-cover isotropy charts in actual Euclidean hyperbolic coordinates. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceArchJacquet SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

abbrev SourceKPFiniteChartStabilizer (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) :=
  MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p

instance sourceKPFiniteChartStabilizer_fintype (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) : Fintype (SourceKPFiniteChartStabilizer K hζ b p) :=
  (sourceKPUpperFiniteChart K hζ b p).finite_stabilizer.fintype

def sourceKPFiniteChartCoordinateDomain (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) : Set (ProductSpace (InfinitePlace K)) :=
  sourceKPArchUpperEuclideanMap K '' (sourceKPUpperFiniteChart K hζ b p).domain

theorem sourceKPFiniteChartCoordinateDomain_upper (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) :
    sourceKPFiniteChartCoordinateDomain K hζ b p ⊆ productUpper (InfinitePlace K) := by
  rintro _ ⟨x,_hx,rfl⟩ v _hv
  exact sourceArchUpperEuclideanMap_positive (x v)

theorem sourceKPFiniteChartCoordinateDomain_isOpen (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) : IsOpen (sourceKPFiniteChartCoordinateDomain K hζ b p) := by
  have hi := (sourceKPArchPositiveHomeomorph K).isOpenMap _
    (sourceKPUpperFiniteChart K hζ b p).isOpen_domain
  have hval := (productUpper_isOpen (InfinitePlace K)).isOpenEmbedding_subtypeVal.isOpenMap _ hi
  simpa only [Set.image_image,Function.comp_def,sourceKPArchPositiveHomeomorph_apply,
    sourceKPFiniteChartCoordinateDomain] using hval

theorem sourceKPFiniteChartCoordinateDomain_mem (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) :
    sourceKPArchUpperEuclideanMap K p ∈ sourceKPFiniteChartCoordinateDomain K hζ b p :=
  ⟨p,(sourceKPUpperFiniteChart K hζ b p).center_mem,rfl⟩

theorem sourceKPFiniteChartCoordinateDomain_invariant (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) (γ : SourceKPFiniteChartStabilizer K hζ b p)
    {x : ProductSpace (InfinitePlace K)} (hx : x ∈ sourceKPFiniteChartCoordinateDomain K hζ b p) :
    sourceKPArchEuclideanAction K hζ γ.val.val x ∈ sourceKPFiniteChartCoordinateDomain K hζ b p := by
  obtain ⟨y,hy,rfl⟩ := hx
  refine ⟨γ.val • y,(sourceKPUpperFiniteChart K hζ b p).domain.smul_mem γ hy,?_⟩
  unfold sourceKPArchEuclideanAction
  rw [sourceKPArchUpperEuclideanMap_left_inverse]
  rfl

theorem sourceKPFiniteChartCoordinateDomain_precompact (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) :
    IsCompact (closure (sourceKPFiniteChartCoordinateDomain K hζ b p)) := by
  have hc := (sourceKPUpperFiniteChart K hζ b p).isCompact_closure.image
    (sourceKPArchUpperEuclideanMap_continuous K)
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  exact Set.image_mono subset_closure

end
end ArtinMatthews
