module

public import ArtinMatthews.SourceKPCuspNativeUpperPoint
public import ArtinMatthews.SourceKPCuspFourierCell
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

/-! Native horizontal slices descend to the actual principal cusp torus.
Integer Fourier coefficients are read on the normalized half-open cell. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceHyperbolicGreen UnitAddTorus
open scoped NumberField AdeleRing MatrixGroups Classical
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K

abbrev sourceKPCuspNativeFinitePeriod (qf : SourceKPFiniteAdeleProjective K hζ) : Prop :=
  ∀ t ∈ sourceKPCuspFiniteIdeal K d,
    ∃ k : sourceKPFiniteDeepMatrixGroup K,
      ((1,qf) : SourceKPAdelicProjective K hζ)⁻¹ *
          sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
        sourceKPFiniteDeepCoverLift K hζ k

variable (qf : SourceKPFiniteAdeleProjective K hζ)
variable (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)

/-- The horizontal slice at positive heights through the original finite point. -/
def sourceKPCuspNativeTraceSlice
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ) (y : V → ℝ) (hy : ∀ v, 0 < y v)
    (t : UnitAddTorus I) : ℂ := by
  let a := sourceKPCuspHeightSection K hζ y hy
  let g : SourceKPAdelicProjective K hζ := (a,qf)
  have hp := sourceKPCuspFinitePeriod_arch_change K hζ d qf hperiod a
  let c := sourceKPCuspLevelCover K hζ d g hp
  exact W (sourceKPAutomorphicCompactMk K hζ
    (c ((sourceKPCuspPrincipalTorusHomeomorph K d hd).symm t)))

theorem sourceKPCuspNativeTraceSlice_mk
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ) (y : V → ℝ) (hy : ∀ v, 0 < y v)
    (a : 𝔸[K]) :
    sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy
        (sourceKPCuspPrincipalTorusHomeomorph K d hd (QuotientAddGroup.mk a)) =
      W (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ
        (sourceKPAdelicUpperLift K hζ a * (sourceKPCuspHeightSection K hζ y hy,qf)))) := by
  rw [sourceKPCuspNativeTraceSlice, ContinuousAddEquiv.symm_apply_apply,
    sourceKPCuspLevelCover_mk]

theorem sourceKPCuspNativeTraceSlice_unitCell
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ) (y : V → ℝ) (hy : ∀ v, 0 < y v)
    (x : I → ℝ) :
    sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy
        (unitTorusUnitCellProjection I x) =
      W (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf)
        (sourceKPCuspProductCoordinates K hζ d hd (x,y))) := by
  rw [← sourceKPCuspUnitCellAdelicPoint_torus K d hd x,
    sourceKPCuspNativeTraceSlice_mk, sourceKPCuspNativeUpperPoint_compact K hζ d hd x y hy qf]

theorem sourceKPCuspNativeTraceSlice_translate
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ) (y : V → ℝ) (hy : ∀ v, 0 < y v)
    (a : 𝔸[K]) (x : I → ℝ) :
    sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy
        (sourceKPCuspPrincipalTorusHomeomorph K d hd (QuotientAddGroup.mk a) +
          unitTorusUnitCellProjection I x) =
      W (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ
        (sourceKPAdelicUpperLift K hζ a *
          (sourceKPAdelicUpperLift K hζ (sourceKPCuspUnitCellAdelicPoint K d hd x) *
            (sourceKPCuspHeightSection K hζ y hy,qf))))) := by
  rw [← sourceKPCuspUnitCellAdelicPoint_torus K d hd x, ← map_add, ← QuotientAddGroup.mk_add,
    sourceKPCuspNativeTraceSlice_mk, sourceKPAdelicUpperLift_add, mul_assoc]

/-- Every integer mode of the literal normalized native principal cell. -/
def sourceKPCuspNativeTraceCellCoeff
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ) (n : I → ℤ) (y : V → ℝ) : ℂ :=
  ∫ x : I → ℝ, mFourier (-n) (unitTorusUnitCellProjection I x) •
    W (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf)
      (sourceKPCuspProductCoordinates K hζ d hd (x,y))) ∂unitTorusUnitCellMeasure I

theorem sourceKPCuspNativeTraceSlice_fourierCoeff
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ) (n : I → ℤ) (y : V → ℝ)
    (hy : ∀ v, 0 < y v) :
    mFourierCoeff (sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy) n =
      sourceKPCuspNativeTraceCellCoeff K hζ d hd qf W n y := by
  have hc : (volume : Measure (I → ℝ)).restrict
      {x : I → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} = unitTorusUnitCellMeasure I := by
    rw [show {x : I → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
      Set.univ.pi (fun _ : I => Set.Ioc (0 : ℝ) 1) by ext x; simp]
    exact Measure.restrict_pi_pi _ _
  rw [mFourierCoeff_eq_integral _ _ (0 : I → ℝ)]
  simp only [Pi.zero_apply, zero_add, hc, sourceKPCuspNativeTraceCellCoeff]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change mFourier (-n) (unitTorusUnitCellProjection I x) •
      sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy
        (unitTorusUnitCellProjection I x) = _
    rw [sourceKPCuspNativeTraceSlice_unitCell]

theorem sourceKPCuspNativeTraceSlice_zero_mode
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ) (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    (∫ t, sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy t
      ∂unitTorusHaar I) = sourceKPCuspNativeTraceCellCoeff K hζ d hd qf W 0 y := by
  let F := sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy
  have h : mFourierCoeff F 0 = ∫ t, F t ∂unitTorusHaar I := by
    unfold mFourierCoeff
    change (∫ t, mFourier (-(0 : I → ℤ)) t • F t ∂unitTorusHaar I) = _
    simp only [neg_zero, mFourier_zero, ContinuousMap.coe_one, Pi.one_apply, one_smul]
  exact h.symm.trans (sourceKPCuspNativeTraceSlice_fourierCoeff K hζ d hd qf hperiod W 0 y hy)

end
end ArtinMatthews
