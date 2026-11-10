module

public import ArtinMatthews.SourceKPCuspNativeArchInvariance
public import ArtinMatthews.SourceKPCuspResidualFourierValue
public import ArtinMatthews.SourceKPAdelicUpperAE
public import ArtinMatthews.SourceKPCuspIntegerResidualMode
public import ArtinMatthews.SourceKPCuspResidualDualProfile
public import ArtinMatthews.SourceKPResidualUpperObstruction
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

/-! All nonzero trace-dual modes of the actual residue cannot vanish:
Fourier completeness would force the upper invariance excluded by genuineness. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Module.Free MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal nonZeroDivisors

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPCuspNativeNonzeroModesVanish_residue_of_values_zero
    (d : 𝓞 K) (hd : d ≠ 0) (qf : Gf) (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)
    {T : ℝ} (hT : 1 ≤ T) (hz : ∀ m : Kˣ, sourceKPCuspResidualFourierValue K hζ m hT qf = 0) :
    sourceKPCuspNativeNonzeroModesVanish K hζ d hd qf
      (fun z => (sourceKPAutomorphicExceptionalResidue K hζ hT).val z) := by
  intro B hB hpos n hn
  let m : Kˣ := Units.mk0 (sourceKPCuspTraceFrequency K d n)
    (sourceKPCuspTraceFrequency_ne_zero K d hd hn)
  have hdual : (m:K) ∈ FractionalIdeal.dual ℤ ℚ
      ((Ideal.span ({d} : Set (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    sourceKPCuspTraceFrequency_mem_dual K d n
  have hprofile := sourceKPCuspResidualFourierCell_ae_eq_value_of_dual K hζ d hd qf
    hperiod m hdual B hB hpos hT
  filter_upwards [hprofile] with y hy
  rw [sourceKPCuspNativeTraceCellCoeff_residue_eq_traceFrequency K hζ d hd qf hT n y]
  change sourceKPCuspResidualFourierCell K hζ d hd qf (m:K) hT y = 0
  simpa only [hz m, zero_mul] using hy

theorem sourceKPCuspResidualFourierValue_exists_ne_zero
    (P : HeightOneSpectrum (𝓞 K)) {T : ℝ} (hT : 1 ≤ T) :
    ∃ (m : Kˣ) (qf : Gf), sourceKPCuspResidualFourierValue K hζ m hT qf ≠ 0 := by
  by_contra h
  have hz (m : Kˣ) (qf : Gf) : sourceKPCuspResidualFourierValue K hζ m hT qf = 0 := by
    by_contra hm
    exact h ⟨m,qf,hm⟩
  let R : Lp ℂ 2 μY := (sourceKPAutomorphicExceptionalResidue K hζ hT).val
  apply sourceKPAutomorphicExceptionalResidue_not_finite_upper_ae K hζ P hT
  intro u
  refine sourceKPAdelicUpper_ae_of_arch_cover_slice K hζ (R : Y → ℂ) ?_ ((0,u) : 𝔸[K])
  intro v qf
  obtain ⟨d,hd,hperiod⟩ := sourceKPAdelicCuspFiniteLevelPeriod K hζ
    ((1,qf) : SourceKPAdelicProjective K hζ)
  exact sourceKPCuspNative_archCover_ae_of_nonzeroModes_zero K hζ d hd qf hperiod R
    (sourceKPCuspNativeNonzeroModesVanish_residue_of_values_zero K hζ d hd qf
      hperiod hT (fun m => hz m qf)) v

end
end ArtinMatthews
