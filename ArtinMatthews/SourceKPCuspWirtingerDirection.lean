module

public import ArtinMatthews.SourceKPCuspProductCoordinates
public import ArtinMatthews.SourceHyperbolicProductCalculus
public import ArtinMatthews.SourceKPCuspTraceFunctional
public import ArtinMatthews.SourceKPCuspNativeHorizontal
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

/-! The scaled principal coordinates identify each actual horizontal
direction with its trace-dual frequency in the normalized Fourier torus. -/
namespace ArtinMatthews
open NumberField Module.Free SourceArchJacquet SourceHyperbolicGreen OAI.CubicEisenstein
open scoped NumberField AdeleRing MatrixGroups Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd
local notation "C" => sourceKPCuspCoordinates K d hd

def sourceKPCuspRealHorizontalDir (v : V) (k : Fin 2) : I → ℝ := by
  letI : IsTotallyComplex K := source_isTotallyComplex K hζ
  exact C (sourceKPCuspHorizontalDirection K v k)

theorem sourceKPCuspRealHorizontalDir_apply (v : V) (k : Fin 2) :
    E (sourceKPCuspRealHorizontalDir K hζ d hd v k,0) = productDirection v k.castSucc := by
  letI : IsTotallyComplex K := source_isTotallyComplex K hζ
  let z := sourceKPCuspHorizontalDirection K v k
  rw [← sourceKPCuspProductHorizontalCLM_direction K v k]
  change E (C z,0) = sourceKPCuspProductHorizontalCLM K z
  funext w
  rw [sourceKPCuspProductCoordinates_apply_arch,ContinuousLinearEquiv.symm_apply_apply]
  have he : sourceKPArchComplexEquiv K hζ w
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z w) =
      sourceKPCuspComplexProjection K w z := by
    exact congrArg (fun a : mixedEmbedding.mixedSpace K =>
      a.2 ⟨w, (source_isTotallyComplex K hζ).isComplex w⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply z)
  rw [he]
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  funext j
  fin_cases j
  · exact (sourceKPCuspProductHorizontalCLM_re K z w).symm
  · exact (sourceKPCuspProductHorizontalCLM_im K z w).symm
  · exact (sourceKPCuspProductHorizontalCLM_height K z w).symm

theorem sourceKPCuspRealHorizontalDir_trace (v : V) (n : I → ℤ) :
    (∑ i, sourceKPCuspRealHorizontalDir K hζ d hd v 0 i * (n i : ℝ)) =
      2 * (v.embedding (sourceKPCuspTraceFrequency K d n)).re ∧
    (∑ i, sourceKPCuspRealHorizontalDir K hζ d hd v 1 i * (n i : ℝ)) =
      -(2 * (v.embedding (sourceKPCuspTraceFrequency K d n)).im) := by
  letI : IsTotallyComplex K := source_isTotallyComplex K hζ
  let m := sourceKPCuspTraceFrequency K d n
  have he (k : Fin 2) : (∑ i, sourceKPCuspRealHorizontalDir K hζ d hd v k i * (n i : ℝ)) =
      sourceKPCuspTraceFunctional K m (sourceKPCuspHorizontalDirection K v k) :=
    (sourceKPCuspTraceFunctional_coordinates K d hd n _).symm
  exact ⟨(he 0).trans (sourceKPCuspTraceFunctional_horizontal_zero K m v),
    (he 1).trans (sourceKPCuspTraceFunctional_horizontal_one K m v)⟩

def sourceKPCuspWirtingerFrequency (ε : Bool) (m : K) (v : V) (y : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) * (y : ℂ) *
    (if ε then star (v.embedding m) else v.embedding m)

theorem sourceKPCuspWirtingerFrequency_zero (ε : Bool) (v : V) (y : ℝ) :
    sourceKPCuspWirtingerFrequency K ε 0 v y = 0 := by
  cases ε <;> simp [sourceKPCuspWirtingerFrequency]

end
end ArtinMatthews
