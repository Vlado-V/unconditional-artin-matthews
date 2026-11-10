module

public import ArtinMatthews.SourceKPCuspPrincipalCellIntegral
public import ArtinMatthews.SourceKPTraceJacquetArchFinite
public import ArtinMatthews.SourceKPAutomorphicEisenstein
public import ArtinMatthews.SourceKPCuspLevelCover
public import ArtinMatthews.SourceEisensteinUpperContinuity
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

/-! Exact nonzero Fourier coefficients on a single principal cusp cell,
with one finite period valid for every archimedean height. -/
namespace ArtinMatthews
open NumberField MeasureTheory StandardAdelic Module.Free
open scoped NumberField AdeleRing MatrixGroups Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K)

local instance sourceFourierCellAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _
local instance sourceFourierCellAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance sourceFourierCellQuotientMeasurable :
    MeasurableSpace (SourceKPCuspPrincipalQuotient K d) := borel _
local instance sourceFourierCellQuotientBorel :
    BorelSpace (SourceKPCuspPrincipalQuotient K d) := ⟨rfl⟩

theorem sourceKPCuspFinitePeriod_arch_change
    (qf : SourceKPFiniteAdeleProjective K hζ)
    (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
      ∃ k : sourceKPFiniteDeepMatrixGroup K,
        (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
          sourceKPFiniteDeepCoverLift K hζ k)
    (a : PGL(2,InfiniteAdeleRing K)) :
    ∀ t ∈ sourceKPCuspFiniteIdeal K d,
      ∃ k : sourceKPFiniteDeepMatrixGroup K,
        (a,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (a,qf) =
          sourceKPFiniteDeepCoverLift K hζ k := by
  intro t ht
  obtain ⟨k,hk⟩ := hperiod t ht
  refine ⟨k,Prod.ext ?_ ?_⟩
  · change a⁻¹ * (sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t)).1 * a = _
    rw [sourceKPAdelicUpperLift_finite_fst,sourceKPFiniteDeepCoverLift_fst,mul_one,inv_mul_cancel]
  · have h := congrArg (fun z : SourceKPAdelicProjective K hζ => z.2) hk
    change qf⁻¹ * (sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t)).2 * qf = _ at h ⊢
    exact h

variable (g : SourceKPAdelicProjective K hζ)
variable (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
  ∃ k : sourceKPFiniteDeepMatrixGroup K,
    g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * g =
      sourceKPFiniteDeepCoverLift K hζ k)

def sourceKPCuspEisensteinCell (s : ℂ) (x : SourceKPCuspPrincipalQuotient K d) : ℂ :=
  sourceKPAutomorphicEisenstein K hζ s (sourceKPCuspLevelCover K hζ d g hperiod x)

theorem sourceKPCuspEisensteinCell_mk (s : ℂ) (x : 𝔸[K]) :
    sourceKPCuspEisensteinCell K hζ d g hperiod s (QuotientAddGroup.mk x) =
      sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ x*g) := by
  exact sourceKPAutomorphicEisenstein_mk K hζ s _

theorem sourceKPCuspEisensteinCell_continuous {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1) :
    Continuous (sourceKPCuspEisensteinCell K hζ d g hperiod s) := by
  apply (QuotientAddGroup.isQuotientMap_mk (sourceKPCuspPrincipalPeriods K d)).continuous_iff.mpr
  simpa only [Function.comp_def,sourceKPCuspEisensteinCell_mk] using
    sourceKPAdelicCompactEisenstein_upper_continuous K hζ hs g

include hperiod in
theorem sourceKPCuspEisensteinCell_traceJacquet {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1)
    (hd : d ≠ 0) (m : Kˣ) (hm : ∃ r : 𝓞 K, (m:K)*(d:K) = (r:K)) :
    (∫ x : ChooseBasisIndex ℤ (𝓞 K) → ℝ,
      star (character K (algebraMap K 𝔸[K] (m:K)*sourceKPCuspUnitCellAdelicPoint K d hd x)) *
        sourceKPAdelicCompactEisenstein K hζ s
          (sourceKPAdelicUpperLift K hζ (sourceKPCuspUnitCellAdelicPoint K d hd x)*g)
      ∂unitTorusUnitCellMeasure (ChooseBasisIndex ℤ (𝓞 K))) =
      (∫ x, sourceKPTraceJacquetArchKernel K hζ m s g.1 x ∂sourceKPArchSelfDualProduct K) *
        ∫ y, sourceKPTraceJacquetFiniteKernel K hζ m s g.2 y ∂sourceKPFiniteStandardHaar K := by
  have h := sourceKPCuspPrincipalFrequency_integral_unitCell K hζ d hd (m:K) hm
    (sourceKPCuspEisensteinCell K hζ d g hperiod s)
    (sourceKPCuspEisensteinCell_continuous K hζ d g hperiod hs).measurable
  simp only [sourceKPCuspEisensteinCell_mk] at h
  exact h.symm.trans (sourceKPAdelicCompactEisenstein_traceJacquet_arch_finite K hζ hs m g)

end
end ArtinMatthews
