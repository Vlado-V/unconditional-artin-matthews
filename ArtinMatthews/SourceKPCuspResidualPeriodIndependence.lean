module

public import ArtinMatthews.SourceKPCuspResidualGeneralFourier
public import ArtinMatthews.SourceKPBandResidueTransfer
public import ArtinMatthews.SourceKPCuspFourierMomentPositive
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The actual residual Fourier coefficient is independent of the valid
principal period used to construct its compact native test. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceHyperbolicGreen Filter
open scoped NumberField AdeleRing MatrixGroups Topology NNReal ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d e : 𝓞 K) (hd : d ≠ 0) (he : e ≠ 0)
variable (qf : SourceKPFiniteAdeleProjective K hζ) (m : Kˣ)
variable (hpd : ∀ t ∈ sourceKPCuspFiniteIdeal K d, ∃ k : sourceKPFiniteDeepMatrixGroup K,
  (1,qf)⁻¹*sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t)*(1,qf) =
    sourceKPFiniteDeepCoverLift K hζ k)
variable (hpe : ∀ t ∈ sourceKPCuspFiniteIdeal K e, ∃ k : sourceKPFiniteDeepMatrixGroup K,
  (1,qf)⁻¹*sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t)*(1,qf) =
    sourceKPFiniteDeepCoverLift K hζ k)
variable (hmd : ∃ r : 𝓞 K, (m:K)*(d:K) = (r:K))
variable (hme : ∃ r : 𝓞 K, (m:K)*(e:K) = (r:K))
variable (cd ce : ℝ≥0) (hcd : 0 < cd) (hce : 0 < ce)
variable (hmapd : Measure.map (sourceKPCuspProductCoordinates K hζ d hd).symm
  (productVolume (InfinitePlace K)) = (cd:ℝ≥0∞) •
    (volume : Measure (ChooseBasisIndex ℤ (𝓞 K) → ℝ)).prod (sourceKPCuspProductHeightMeasure K))
variable (hmape : Measure.map (sourceKPCuspProductCoordinates K hζ e he).symm
  (productVolume (InfinitePlace K)) = (ce:ℝ≥0∞) •
    (volume : Measure (ChooseBasisIndex ℤ (𝓞 K) → ℝ)).prod (sourceKPCuspProductHeightMeasure K))

include hpd hpe hmd hme hcd hce hmapd hmape in
theorem sourceKPCuspResidualCoefficient_period_independent {T : ℝ} (hT : 1 ≤ T) :
    sourceKPCuspResidualCoefficient K hζ d hd qf m cd hT =
      sourceKPCuspResidualCoefficient K hζ e he qf m ce hT := by
  let B := sourceKPCuspHeightBox K
  let hB := sourceKPCuspHeightBox_isCompact K
  let hp := sourceKPCuspHeightBox_positive K
  let F := sourceKPCuspNativeFourierTest K hζ d hd qf B hB hp (m:K) hT
  let G := sourceKPCuspNativeFourierTest K hζ e he qf B hB hp (m:K) hT
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsPreconnected U :=
    ((convex_Ioi (𝕜 := ℝ) (0:ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have hF : MeromorphicOn (fun z => (ce:ℂ)*F z) U := fun z hz =>
    (show AnalyticAt ℂ (fun _ : ℂ => (ce:ℂ)) z from analyticAt_const).meromorphicAt.mul
      (sourceKPCuspNativeFourierTest_meromorphic K hζ d hd qf B hB hp (m:K) hT z hz)
  have hG : MeromorphicOn (fun z => (cd:ℂ)*G z) U := fun z hz =>
    (show AnalyticAt ℂ (fun _ : ℂ => (cd:ℂ)) z from analyticAt_const).meromorphicAt.mul
      (sourceKPCuspNativeFourierTest_meromorphic K hζ e he qf B hB hp (m:K) hT z hz)
  let b : ℝ := ((3*(Module.finrank ℚ K+1):ℕ):ℝ)
  let a : ℂ := b
  have hb : 0 < b := by dsimp only [b]; positivity
  have ha : a ∈ U := by change 0 < a.re; simpa only [a,Complex.ofReal_re] using hb
  have hab : b/2 < a.re := by simp only [a,Complex.ofReal_re]; linarith
  have hinit : (fun z => (ce:ℂ)*F z) =ᶠ[𝓝 a] (fun z => (cd:ℂ)*G z) := by
    filter_upwards [(Complex.continuous_re.tendsto a).eventually (Ioi_mem_nhds hab)] with z hz
    have hz' : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*z.re+1 := by
      change b ≤ 2*z.re+1
      linarith
    dsimp only [F,G]
    rw [sourceKPCuspNativeFourierTest_initial_factor_of_measure K hζ d hd qf hpd
      B hB hp m hmd cd hcd hmapd T hT z hz',
      sourceKPCuspNativeFourierTest_initial_factor_of_measure K hζ e he qf hpe
      B hB hp m hme ce hce hmape T hT z hz']
    ring
  have heq := sourceKPMeromorphicOn_eventuallyEq_of_germ hF hG hU ha
    (show (1/6:ℂ) ∈ U by change 0 < (1/6:ℂ).re; norm_num) hinit
  have hdlim := sourceKPCuspNativeFourierTest_residue_tendsto K hζ d hd qf B hB hp (m:K) hT
  have helim := sourceKPCuspNativeFourierTest_residue_tendsto K hζ e he qf B hB hp (m:K) hT
  have hleft : Tendsto (fun z => (z-1/6)*((ce:ℂ)*F z)) (𝓝[≠] (1/6:ℂ))
      (𝓝 ((ce:ℂ)*sourceKPCuspNativeFourierResidue K hζ d hd qf B hB hp (m:K) hT)) := by
    simpa only [F,mul_left_comm,mul_assoc] using (tendsto_const_nhds.mul hdlim)
  have hright : Tendsto (fun z => (z-1/6)*((cd:ℂ)*G z)) (𝓝[≠] (1/6:ℂ))
      (𝓝 ((cd:ℂ)*sourceKPCuspNativeFourierResidue K hζ e he qf B hB hp (m:K) hT)) := by
    simpa only [G,mul_left_comm,mul_assoc] using (tendsto_const_nhds.mul helim)
  have hc : (ce:ℂ)*sourceKPCuspNativeFourierResidue K hζ d hd qf B hB hp (m:K) hT =
      (cd:ℂ)*sourceKPCuspNativeFourierResidue K hζ e he qf B hB hp (m:K) hT := by
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [heq] with z hz
    exact congrArg (fun w : ℂ => (z-1/6)*w) hz.symm
  have hdC : (cd:ℂ) ≠ 0 := by exact_mod_cast hcd.ne'
  have heC : (ce:ℂ) ≠ 0 := by exact_mod_cast hce.ne'
  have hA := sourceKPCuspArchFourierMoment_oneSixth_ne_zero K hζ m
  unfold sourceKPCuspResidualCoefficient
  field_simp [hdC,heC,hA]
  dsimp only [B,hB,hp] at hc
  linear_combination hc

end
end ArtinMatthews
