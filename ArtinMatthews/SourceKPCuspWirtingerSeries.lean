module

public import ArtinMatthews.SourceKPReflectionHorizontalProduct
public import ArtinMatthews.SourceKPCuspNativeTraceSlice
public import ArtinMatthews.SourceKPCuspWirtingerDirection
public import ArtinMatthews.SourceKPCuspNativeSmoothSlice
public import ArtinMatthews.SourceKPCuspWirtingerTorus
public import ArtinMatthews.UnitTorusSmoothFourier
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

/-! The product of native horizontal derivatives has its literal
Fourier expansion at the zero horizontal coordinate. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory UnitAddTorus SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Classical ContDiff BigOperators
noncomputable section

local instance sourceKPWirtingerSeriesCircleMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd
local notation "P" => unitTorusUnitCellProjection I
local notation "Ω" => productUpper V

def sourceKPCuspWirtingerProductFrequency (ε : V → Bool) (l : List V) (m : K)
    (y : V → ℝ) : ℂ :=
  (l.map (fun v => sourceKPCuspWirtingerFrequency K (ε v) m v (y v))).prod

theorem sourceKPCuspWirtingerProductFrequency_zero (ε : V → Bool) (l : List V) (hl : l ≠ [])
    (y : V → ℝ) :
    sourceKPCuspWirtingerProductFrequency K ε l 0 y = 0 := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons v l =>
    simp [sourceKPCuspWirtingerProductFrequency,sourceKPCuspWirtingerFrequency_zero]

theorem sourceKPCuspWirtingerTorusList_exists (ε : V → Bool) (l : List V) (y : V → ℝ)
    (hy : ∀ w, 0 < y w) (U : X → ℂ) (hU : ∀ p ∈ Ω, ContDiffAt ℝ (∞ : ℕ∞ω) U p)
    (F : C(UnitAddTorus I, ℂ))
    (hF : ContDiff ℝ (∞ : ℕ∞ω) (fun x : I → ℝ => F (P x)))
    (he : ∀ x : I → ℝ, F (P x) = U (E (x,y))) :
    ∃ G : C(UnitAddTorus I, ℂ),
      ContDiff ℝ (∞ : ℕ∞ω) (fun x : I → ℝ => G (P x)) ∧
      (∀ x : I → ℝ, G (P x) = sourceProductHorizontalList ε l U (E (x,y))) ∧
      ∀ n : I → ℤ, mFourierCoeff G n =
        sourceKPCuspWirtingerProductFrequency K ε l (sourceKPCuspTraceFrequency K d n) y *
          mFourierCoeff F n := by
  induction l with
  | nil =>
    exact ⟨F,hF,he,fun _ => by simp [sourceKPCuspWirtingerProductFrequency]⟩
  | cons v l ih =>
    obtain ⟨G,hG,hGx,hGF⟩ := ih
    let U₁ := sourceProductHorizontalList ε l U
    have hs (p : X) (hp : p ∈ Ω) : DifferentiableAt ℝ U₁ p :=
      (sourceProductHorizontalList_contDiffAt ε l (hU p hp)).differentiableAt (by simp)
    obtain ⟨H,hH,hHx,hHG⟩ := sourceKPCuspWirtingerTorus_exists K hζ d hd (ε v) v y hy U₁ hs G hG hGx
    refine ⟨H,hH,hHx,fun n => ?_⟩
    rw [hHG,hGF]
    simp only [sourceKPCuspWirtingerProductFrequency,List.map_cons,List.prod_cons,mul_assoc]

theorem sourceKPCuspProductCoordinates_zero (y : V → ℝ) :
    E (0,y) = sourceKPCuspHeightPoint K y := by
  funext v
  rw [sourceKPCuspProductCoordinates_apply_arch]
  have hz : (0 : InfiniteAdeleRing K) v = (0 : v.Completion) := rfl
  simp [sourceKPCuspHeightPoint, hz]

theorem sourceKPCuspNativeHorizontal_hasSum
    (qf : SourceKPFiniteAdeleProjective K hζ) (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (hW : ContDiffOn ℝ (∞ : ℕ∞ω) (sourceKPCompactChartPullback K hζ W (QuotientGroup.mk qf)) Ω)
    (ε : V → Bool) (l : List V) (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    HasSum (fun n : I → ℤ =>
      sourceKPCuspWirtingerProductFrequency K ε l (sourceKPCuspTraceFrequency K d n) y *
        sourceKPCuspNativeTraceCellCoeff K hζ d hd qf W n y)
      (sourceProductHorizontalList ε l (sourceKPCompactChartPullback K hζ W (QuotientGroup.mk qf))
        (sourceKPCuspHeightPoint K y)) := by
  let U := sourceKPCompactChartPullback K hζ W (QuotientGroup.mk qf)
  let f := sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy
  let F : C(UnitAddTorus I, ℂ) := ⟨f, sourceKPCuspNativeTraceSlice_continuous K hζ d hd qf hperiod W hW y hy⟩
  have hF := sourceKPCuspNativeTraceSlice_lift_contDiff K hζ d hd qf hperiod W hW y hy
  have he := sourceKPCuspNativeTraceSlice_lift_eq_chart K hζ d hd qf hperiod W y hy
  obtain ⟨G,hG,hGx,hGF⟩ := sourceKPCuspWirtingerTorusList_exists K hζ d hd ε l y hy U
    (fun p hp => (hW p hp).contDiffAt ((productUpper_isOpen V).mem_nhds hp)) F hF he
  have h := unitTorus_hasSum_mFourier_of_smooth I G G.continuous hG (P 0)
  rw [hGx,sourceKPCuspProductCoordinates_zero K hζ d hd y] at h
  apply h.congr_fun
  intro n
  have hm : mFourier n (P 0) = 1 := by
    simp [mFourier,unitTorusUnitCellProjection,fourier_coe_apply]
  rw [hm,one_mul,hGF]
  change _ * sourceKPCuspNativeTraceCellCoeff K hζ d hd qf W n y =
    _ * mFourierCoeff f n
  rw [sourceKPCuspNativeTraceSlice_fourierCoeff K hζ d hd qf hperiod W n y hy]

end
end ArtinMatthews
