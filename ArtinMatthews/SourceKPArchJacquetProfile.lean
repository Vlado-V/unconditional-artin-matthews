module

public import ArtinMatthews.SourceArchWeightedProduct
public import ArtinMatthews.SourceKPArchJacquetDiagonal
public import ArtinMatthews.SourceKPTraceJacquetArchProduct
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

/-! The actual local trace character and self-dual Haar produce the
normalized Fourier profile at every complex parameter in Re(s)>0. -/
namespace ArtinMatthews
open NumberField MeasureTheory Matrix StandardAdelic SourceArchJacquet
open OAI.RepresentationTheory.Weil
open scoped NumberField AdeleRing MatrixGroups BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceProfileCompletionMeasurable (v : InfinitePlace K) : MeasurableSpace v.Completion := borel _
local instance sourceProfileCompletionBorel (v : InfinitePlace K) : BorelSpace v.Completion := ⟨rfl⟩
local instance sourceProfileInfiniteMeasurable : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ v : InfinitePlace K, v.Completion))
local instance sourceProfileInfiniteDecEq : DecidableEq (InfinitePlace K) := Classical.decEq _

theorem sourceArchTraceCharacter_continuous :
    Continuous (sourceArchTraceCharacter : ℂ → ℂ) := by
  have he : (sourceArchTraceCharacter : ℂ → ℂ) = fun z => sourceArchJacquetPhase (-z) := by
    funext z
    rw [sourceArchJacquetPhase_eq,neg_neg]
  rw [he]
  exact sourceArchJacquetPhase_continuous.comp continuous_neg

theorem sourceArchTraceCharacter_norm (z : ℂ) : ‖sourceArchTraceCharacter z‖ = 1 := by
  rw [show sourceArchTraceCharacter z = sourceArchJacquetPhase (-z) by
    rw [sourceArchJacquetPhase_eq,neg_neg]]
  exact sourceArchJacquetPhase_norm _

theorem sourceKPTraceJacquetLocalArchKernel_diagonal_profile (m : Kˣ) (s : ℂ)
    (y : (v : InfinitePlace K) → v.Completionˣ) (v : InfinitePlace K)
    (hv : InfinitePlace.IsComplex v) :
    (∫ x, sourceKPTraceJacquetLocalArchKernel K hζ m s (sourceKPArchJacquetDiagonal K y) v x
      ∂Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion (localInfiniteCharacter K v)) =
      sourceArchWeightedDiagonalProfile sourceArchTraceCharacter s
        (-(sourceKPArchComplexEquiv K hζ v (algebraMap K v.Completion (m:K)))) ‖(y v : v.Completion)‖ := by
  let e := sourceArchCompletionEquiv K v hv
  let yC := Units.map e.toMonoidHom (y v)
  let a : ℂ := -(e (algebraMap K v.Completion (m:K)))
  let F : ℂ → ℂ := fun z => sourceArchTraceCharacter (a*z) *
    sourceArchSphericalSection s (sourcePGL2Weyl*sourcePGL2Upper z*sourcePGL2Diagonal yC)
  have hF : (fun x => sourceKPTraceJacquetLocalArchKernel K hζ m s (sourceKPArchJacquetDiagonal K y) v x) =
      fun x => F (e x) := by
    funext x
    rw [sourceKPTraceJacquetLocalArchKernel,sourceKPLocalInfiniteCharacter_star,
      sourceKPArchJacquetDiagonal_localSection K hζ s y v hv,
      sourceArchCompletedSphericalSection_bigCell,sourceArchCompletion_character K v hv]
    simp only [map_neg,map_mul]
    dsimp only [F,a,e,yC]
    rw [neg_mul]
  rw [hF]
  have hi := sourceArchCompletion_integral K v hv F
  rw [hi,← sourceArchWeightedDiagonalProfile_eq_integral sourceArchTraceCharacter s a yC]
  have hn : ‖(yC : ℂ)‖ = ‖(y v : v.Completion)‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).isometry.norm_map_of_map_zero
      (map_zero e) _
  rw [hn]
  rfl

def sourceKPTraceJacquetProfileFrequency (m : Kˣ) (v : InfinitePlace K) : ℂ :=
  -(sourceKPArchComplexEquiv K hζ v (algebraMap K v.Completion (m:K)))

def sourceKPTraceJacquetArchProfile (m : Kˣ) (s : ℂ) (y : InfinitePlace K → ℝ) : ℂ :=
  sourceArchWeightedProduct (fun _ : InfinitePlace K => sourceArchTraceCharacter)
    (sourceKPTraceJacquetProfileFrequency K hζ m) s y

theorem sourceKPTraceJacquetArch_diagonal_profile {s : ℂ} (hs : 0 < s.re)
    (m : Kˣ) (y : (v : InfinitePlace K) → v.Completionˣ) :
    (∫ x, sourceKPTraceJacquetArchKernel K hζ m s (sourceKPArchJacquetDiagonal K y) x
      ∂sourceKPArchSelfDualProduct K) =
      sourceKPTraceJacquetArchProfile K hζ m s (fun v => ‖(y v : v.Completion)‖) := by
  let := source_isTotallyComplex K hζ
  rw [(sourceKPTraceJacquetArchKernel_integral_product K hζ hs m _).2]
  apply Finset.prod_congr rfl
  intro v _
  exact sourceKPTraceJacquetLocalArchKernel_diagonal_profile K hζ m s y v
    (IsTotallyComplex.isComplex v)

theorem sourceKPTraceJacquetArchProfile_analyticOnNhd (m : Kˣ) (y : InfinitePlace K → ℝ)
    (hy : ∀ v, 0 < y v) :
    AnalyticOnNhd ℂ (fun s => sourceKPTraceJacquetArchProfile K hζ m s y) {s : ℂ | 0 < s.re} :=
  sourceArchWeightedProduct_analyticOnNhd (fun _ => sourceArchTraceCharacter)
    (fun _ => sourceArchTraceCharacter_continuous)
    (fun _ x => (sourceArchTraceCharacter_norm x).le)
    (sourceKPTraceJacquetProfileFrequency K hζ m) y hy

end
end ArtinMatthews
