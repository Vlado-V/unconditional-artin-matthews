module

public import ArtinMatthews.SourceFiniteFiberScattering
public import ArtinMatthews.SourceKPCuspNativeFourierTest
public import ArtinMatthews.SourceKPCuspPowerMoment
public import ArtinMatthews.SourceKPBandResidueTransfer
public import ArtinMatthews.SourceKPCuspZeroInitialMoment
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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

namespace ArtinMatthews
open NumberField Module.Free MeasureTheory Filter StandardAdelic SourceHyperbolicGreen
open scoped NumberField AdeleRing MatrixGroups Topology NNReal ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0) (qf : SourceKPFiniteAdeleProjective K hζ)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd
variable (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
  ∃ k : sourceKPFiniteDeepMatrixGroup K,
    (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
      sourceKPFiniteDeepCoverLift K hζ k)

include hperiod in
theorem sourceKPCuspNativeZeroResidue_eq
    (c : ℝ≥0) (hc : 0 < c)
    (hmap : Measure.map (E).symm (productVolume V) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hM : ∀ s : ℂ, ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1 →
      sourceKPAdelicTraceIntertwiner K hζ s (1,qf) =
        sourceKPFiniteFiberScatteringContinuation K hζ qf S s)
    (B : Set (V → ℝ)) (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v)
    {T : ℝ} (hT : 1 ≤ T) :
    sourceKPCuspNativeFourierResidue K hζ d hd qf B hB hpos (0:K) hT =
      (c:ℂ) * sourceKPFiniteFiberScatteringResidue K hζ qf S *
        sourceKPCuspPowerMoment K B (-(1/6:ℂ)) := by
  let F := sourceKPCuspNativeFourierTest K hζ d hd qf B hB hpos (0:K) hT
  let J := sourceKPCuspPowerMoment K B
  let A (s : ℂ) := (c:ℂ) * (J s * sourceKPAdelicCompactScalar K hζ s (1,qf))
  let M := sourceKPFiniteFiberScatteringContinuation K hζ qf S
  let G (s : ℂ) := A s + (c:ℂ) * M s * J (-s)
  let U : Set ℂ := {s | 0 < s.re}
  have hU : IsPreconnected U :=
    ((convex_Ioi (𝕜 := ℝ) (0:ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have hF : MeromorphicOn F U :=
    sourceKPCuspNativeFourierTest_meromorphic K hζ d hd qf B hB hpos (0:K) hT
  have hJ : Differentiable ℂ J := sourceKPCuspPowerMoment_entire K hζ d hd B hB hpos
  have hA : Differentiable ℂ A :=
    (differentiable_const (c:ℂ)).mul (hJ.mul (sourceKPAdelicCompactScalar_entire K hζ (1,qf)))
  have hJn : Differentiable ℂ (fun s => J (-s)) := hJ.comp differentiable_neg
  have hG : MeromorphicOn G U := by
    intro s hs
    have hconst : MeromorphicAt (fun _ : ℂ => (c:ℂ)) s := analyticAt_const.meromorphicAt
    exact (hA.analyticAt s).meromorphicAt.add
      ((hconst.mul (sourceKPFiniteFiberScatteringContinuation_meromorphicOn K hζ qf S s hs)).mul
        (hJn.analyticAt s).meromorphicAt)
  let deg : ℝ := ((3*(Module.finrank ℚ K+1):ℕ):ℝ)
  let a : ℂ := deg
  have ha : a ∈ U := by
    change 0 < (deg:ℂ).re
    simp only [Complex.ofReal_re]
    dsimp only [deg]
    positivity
  have hfar : deg/2 < a.re := by
    change deg/2 < deg
    have hp : 0 < deg := by dsimp only [deg]; positivity
    linarith
  have he : F =ᶠ[𝓝 a] G := by
    filter_upwards [(Complex.continuous_re.tendsto a).eventually (Ioi_mem_nhds hfar)] with s hs
    have hs' : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1 := by
      change deg ≤ 2*s.re+1
      linarith
    dsimp only [F,G,A,M,J]
    rw [sourceKPCuspNativeZeroTest_initial K hζ d hd qf hperiod c hc hmap B hB hpos hT hs',hM s hs']
    ring
  have hec := sourceKPMeromorphicOn_eventuallyEq_of_germ hF hG hU ha
    (show (1/6:ℂ) ∈ U by norm_num [U]) he
  have hA_lim : Tendsto A (𝓝[≠] (1/6:ℂ)) (𝓝 (A (1/6))) :=
    (hA.continuous.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hJ_lim : Tendsto (fun s => J (-s)) (𝓝[≠] (1/6:ℂ)) (𝓝 (J (-(1/6:ℂ)))) :=
    (hJn.continuous.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hsmall : Tendsto (fun s : ℂ => s-1/6) (𝓝[≠] (1/6:ℂ)) (𝓝 0) := by
    simpa only [sub_self] using
      ((show Continuous (fun s : ℂ => s-(1/6:ℂ)) from
        continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
        (show 𝓝[≠] (1/6:ℂ) ≤ 𝓝 (1/6:ℂ) from nhdsWithin_le_nhds))
  have hMR := sourceKPFiniteFiberScatteringResidue_tendsto K hζ qf S
  have hlim : Tendsto (fun s : ℂ => (s-1/6)*A s + (c:ℂ)*((s-1/6)*M s)*J (-s))
      (𝓝[≠] (1/6:ℂ))
      (𝓝 ((c:ℂ)*sourceKPFiniteFiberScatteringResidue K hζ qf S*J (-(1/6:ℂ)))) := by
    simpa only [zero_mul,zero_add] using
      (hsmall.mul hA_lim).add ((hMR.const_mul (c:ℂ)).mul hJ_lim)
  have hlimG : Tendsto (fun s : ℂ => (s-1/6)*G s) (𝓝[≠] (1/6:ℂ))
      (𝓝 ((c:ℂ)*sourceKPFiniteFiberScatteringResidue K hζ qf S*J (-(1/6:ℂ)))) := by
    apply hlim.congr'
    filter_upwards with s
    dsimp only [G]
    ring
  have hlimF : Tendsto (fun s : ℂ => (s-1/6)*F s) (𝓝[≠] (1/6:ℂ))
      (𝓝 ((c:ℂ)*sourceKPFiniteFiberScatteringResidue K hζ qf S*J (-(1/6:ℂ)))) := by
    apply hlimG.congr'
    filter_upwards [hec] with s hs
    rw [hs]
  exact tendsto_nhds_unique
    (sourceKPCuspNativeFourierTest_residue_tendsto K hζ d hd qf B hB hpos (0:K) hT) hlimF

include hperiod in
theorem sourceKPCuspNativeZeroResidue_formula
    (c : ℝ≥0) (hc : 0 < c)
    (hmap : Measure.map (E).symm (productVolume V) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K))
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
      S₀ ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      ∀ (T : ℝ) (hT : 1 ≤ T) (B : Set (V → ℝ)) (hB : IsCompact B)
        (hpos : ∀ y ∈ B, ∀ v, 0 < y v),
        sourceKPCuspNativeFourierResidue K hζ d hd qf B hB hpos (0:K) hT =
          (c:ℂ) * sourceKPFiniteFiberScatteringResidue K hζ qf S *
            sourceKPCuspPowerMoment K B (-(1/6:ℂ)) := by
  obtain ⟨S,hS,hH,hbad,hM,_,_⟩ := sourceKPFiniteFiberScatteringContinuation_exists K hζ qf S₀
  exact ⟨S,hS,hH,hbad,fun T hT B hB hpos =>
    sourceKPCuspNativeZeroResidue_eq K hζ d hd qf hperiod c hc hmap S hM B hB hpos hT⟩

end
end ArtinMatthews
