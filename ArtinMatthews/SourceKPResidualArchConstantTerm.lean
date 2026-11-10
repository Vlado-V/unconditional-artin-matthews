module

public import ArtinMatthews.SourceKPResidualArchMean
public import ArtinMatthews.SourceFiniteFiberScattering
public import ArtinMatthews.SourceKPAutomorphicSpectralFamily
public import ArtinMatthews.SourceKPCuspHeightConstantTerm
public import ArtinMatthews.SourceKPCuspHeightAE
public import ArtinMatthews.SourceKPCuspPrincipalFrequency
public import ArtinMatthews.SourceKPCuspZeroResidueCoefficient
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

/-! A single scattering window gives the actual normalized constant term
on almost every full archimedean frame, with all height shapes retained. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic UnitAddTorus
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "G" => PGL(2, InfiniteAdeleRing K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "V" => InfinitePlace K
local notation "μA" => sourceKPArchHaar K hζ
local notation "μD" => Measure.restrict (sourceKPAdelicTraceProduct K) (sourceKPAdelicFundamentalDomain K)
local notation "μh" => sourceKPCuspProductHeightMeasure K
local notation "H" => sourceKPCuspRepresentativeHeight K hζ
local notation "p" => sourceKPCuspArchRepresentativeCoordinates K hζ
local instance sourceResidualArchCTAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _
local instance sourceResidualArchCTCircleMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

theorem sourceKPResidualTraceOrbit_integrable_ae {T : ℝ} (hT : 1 ≤ T) (qf : Gf) :
    ∀ᵐ a ∂μA, Integrable (sourceKPCompactTraceOrbit K hζ
      (sourceKPAutomorphicExceptionalResidue K hζ hT).val a qf) μD := by
  obtain ⟨d,hd,_,hp⟩ := sourceKPAdelicCuspFrequencyPeriod K hζ (0:K) (1,qf)
  let R := (sourceKPAutomorphicExceptionalResidue K hζ hT).val
  exact sourceKPCompactTraceOrbit_integrable_ae K hζ d hd R (Lp.memLp R) qf hp

theorem sourceKPResidualTraceMean_ae_eq_scattering
    {T : ℝ} (hT : 1 ≤ T) (qf : Gf) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hM : ∀ s : ℂ, ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1 →
      sourceKPAdelicTraceIntertwiner K hζ s (1,qf) =
        sourceKPFiniteFiberScatteringContinuation K hζ qf S s) :
    ∀ᵐ a ∂μA, sourceKPCompactTraceMean K hζ
      (sourceKPAutomorphicExceptionalResidue K hζ hT).val a qf =
        sourceKPFiniteFiberScatteringResidue K hζ qf S *
          ((sourceKPCuspArchHeight K (H a) ^ (1/3:ℝ) : ℝ) : ℂ) := by
  obtain ⟨d,hd,_,hp⟩ := sourceKPAdelicCuspFrequencyPeriod K hζ (0:K) (1,qf)
  let E := sourceKPCuspProductCoordinates K hζ d hd
  let R := (sourceKPAutomorphicExceptionalResidue K hζ hT).val
  have hzero (y : V → ℝ) : sourceKPCuspNativeTraceCellCoeff K hζ d hd qf R 0 y =
      sourceKPCuspResidualFourierCell K hζ d hd qf (0:K) hT y := by
    unfold sourceKPCuspNativeTraceCellCoeff sourceKPCuspResidualFourierCell
    simp only [neg_zero, mFourier_zero, ContinuousMap.coe_one, Pi.one_apply, one_smul,
      map_zero,zero_mul,AddChar.map_zero_eq_one,star_one,one_mul,R]
  have he : ∀ᵐ y ∂μh, sourceKPCuspNativeTraceCellCoeff K hζ d hd qf R 0 y =
      sourceKPFiniteFiberScatteringResidue K hζ qf S *
        ((sourceKPCuspArchHeight K y ^ (1/3:ℝ) : ℝ) : ℂ) := by
    apply sourceKPCuspProductHeight_ae_of_compact K
    intro B hB hpos
    exact (sourceKPCuspResidualZeroCell_ae_eq K hζ d hd qf hp S hM hT B hB hpos).mono
      (fun y hy => (hzero y).trans hy)
  have hheight := sourceKPCuspArchCellHeight_quasiMeasurePreserving K hζ d hd
  filter_upwards [hheight.ae he,hheight.ae (sourceKPCuspProductHeight_ae_positive K)] with a ha hy
  let x := (E.symm (p a)).1
  let y := (E.symm (p a)).2
  have hpa : p a = E (x,y) := (E.apply_symm_apply (p a)).symm
  calc
    _ = sourceKPCuspNativeTraceCellCoeff K hζ d hd qf R 0 y :=
      sourceKPCompactTraceMean_eq_nativeCell K hζ d hd R (Lp.stronglyMeasurable R).measurable
        a qf hp x y hy hpa
    _ = _ := by
      rw [← sourceKPCuspRepresentativeHeight_eq K hζ d hd a]
      exact ha

end
end ArtinMatthews
