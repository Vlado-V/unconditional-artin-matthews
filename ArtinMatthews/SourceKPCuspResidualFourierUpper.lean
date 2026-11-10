module

public import ArtinMatthews.SourceKPCuspResidualFourierValue
public import ArtinMatthews.SourceKPBandResidueTransfer
public import ArtinMatthews.SourceKPCuspHeightJacquetProfile
public import ArtinMatthews.SourceKPTraceJacquetUpper
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

/-! The literal compact Fourier moment inherits the upper-root phase of
the initial trace Jacquet integral, and so does its residue. -/
namespace ArtinMatthews

open NumberField Matrix MeasureTheory Module.Free SourceHyperbolicGreen StandardAdelic Filter
open scoped NumberField MatrixGroups AdeleRing BigOperators NNReal ENNReal Topology

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "V" => InfinitePlace K
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
local notation "ψ[" m ", " u "]" => finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m:K) * u)
local notation "E[" d ", " hd "]" => sourceKPCuspProductCoordinates K hζ d hd

private theorem jacquet_moment_left_finite_upper (m : Kˣ) (qf : Gf) (u : 𝔸ᶠ[K])
    (B : Set (V → ℝ)) (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v)
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1) :
    sourceKPCuspArchFourierMoment K hζ m B s *
        (∫ z, sourceKPTraceJacquetFiniteKernel K hζ m s (Nf u*qf) z ∂sourceKPFiniteStandardHaar K) =
      ψ[m, u] * (sourceKPCuspArchFourierMoment K hζ m B s *
        (∫ z, sourceKPTraceJacquetFiniteKernel K hζ m s qf z ∂sourceKPFiniteStandardHaar K)) := by
  let Q := Nf u*qf
  let A := sourceKPTraceJacquetArchProfile K hζ m s
  let F (g : Gf) := ∫ z, sourceKPTraceJacquetFiniteKernel K hζ m s g z ∂sourceKPFiniteStandardHaar K
  have hspos : 0 < s.re := by
    have hdeg : 0 ≤ (Module.finrank ℚ K:ℝ) := Nat.cast_nonneg _
    push_cast at hs
    linarith
  have hphase : character K (algebraMap K 𝔸[K] (m:K)*sourceKPFiniteAddEmbedding K u) = ψ[m, u] := by
    rw [show algebraMap K 𝔸[K] (m:K)*sourceKPFiniteAddEmbedding K u =
      (0,algebraMap K 𝔸ᶠ[K] (m:K)*u) from Prod.ext (mul_zero _) rfl, character_finite]
  have hp (y : V → ℝ) (hy : y ∈ B) : A y * F Q = ψ[m, u] * (A y * F qf) := by
    let a := sourceKPCuspHeightSection K hζ y (hpos y hy)
    have hu : sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K u) * (a,qf) = (a,Q) := by
      apply Prod.ext
      · change ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) 0) * a = a
        rw [sourceKPUpperMatrix_zero, map_one, one_mul]
      · rfl
    have h := sourceKPAdelicCompactEisenstein_traceJacquet_left_upper K hζ hs m (a,qf) (sourceKPFiniteAddEmbedding K u)
    rw [hu, hphase, sourceKPAdelicCompactEisenstein_traceJacquet_arch_finite K hζ hs m (a,Q),
      sourceKPAdelicCompactEisenstein_traceJacquet_arch_finite K hζ hs m (a,qf)] at h
    change (∫ x, sourceKPTraceJacquetArchKernel K hζ m s a x ∂sourceKPArchSelfDualProduct K) *
      F Q = ψ[m, u] * ((∫ x, sourceKPTraceJacquetArchKernel K hζ m s a x
        ∂sourceKPArchSelfDualProduct K) * F qf) at h
    rw [sourceKPCuspHeightSection_arch_jacquet K hζ hspos m y (hpos y hy)] at h
    exact h
  change (∫ y in B, A y ∂sourceKPCuspProductHeightMeasure K) * F Q =
    ψ[m, u] * ((∫ y in B, A y ∂sourceKPCuspProductHeightMeasure K) * F qf)
  calc
    _ = ∫ y in B, A y * F Q ∂sourceKPCuspProductHeightMeasure K :=
      (integral_mul_const (F Q) A).symm
    _ = ∫ y in B, ψ[m, u] * (A y * F qf) ∂sourceKPCuspProductHeightMeasure K :=
      setIntegral_congr_fun hB.measurableSet hp
    _ = _ := by rw [integral_const_mul, integral_mul_const]

theorem sourceKPCuspNativeFourierTest_left_finite_upper_initial
    (m : Kˣ) (qf : Gf) (u : 𝔸ᶠ[K]) (d : 𝓞 K) (hd : d ≠ 0)
    (hm : ∃ r : 𝓞 K, (m:K)*(d:K) = (r:K))
    (hp : ∀ t ∈ sourceKPCuspFiniteIdeal K d, ∃ k : sourceKPFiniteDeepMatrixGroup K,
      (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
        sourceKPFiniteDeepCoverLift K hζ k)
    (hp' : ∀ t ∈ sourceKPCuspFiniteIdeal K d, ∃ k : sourceKPFiniteDeepMatrixGroup K,
      (1,Nf u*qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,Nf u*qf) =
        sourceKPFiniteDeepCoverLift K hζ k)
    (c : ℝ≥0) (hc : 0 < c)
    (hmap : Measure.map (E[d, hd]).symm (productVolume V) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K))
    (B : Set (V → ℝ)) (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v)
    {T : ℝ} (hT : 1 ≤ T) {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1) :
    sourceKPCuspNativeFourierTest K hζ d hd (Nf u*qf) B hB hpos (m:K) hT s =
      ψ[m, u] * sourceKPCuspNativeFourierTest K hζ d hd qf B hB hpos (m:K) hT s := by
  rw [sourceKPCuspNativeFourierTest_initial_factor_of_measure K hζ d hd (Nf u*qf)
      hp' B hB hpos m hm c hc hmap T hT s hs,
    sourceKPCuspNativeFourierTest_initial_factor_of_measure K hζ d hd qf
      hp B hB hpos m hm c hc hmap T hT s hs,
    mul_assoc, jacquet_moment_left_finite_upper K hζ m qf u B hB hpos hs]
  ring

theorem sourceKPCuspResidualFourierValue_left_finite_upper
    (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (qf : Gf) (u : 𝔸ᶠ[K]) :
    sourceKPCuspResidualFourierValue K hζ m hT (Nf u*qf) =
      ψ[m, u] * sourceKPCuspResidualFourierValue K hζ m hT qf := by
  let Q := Nf u*qf
  let g : Bool → SourceKPAdelicProjective K hζ
    | false => (1,qf)
    | true => (1,Q)
  obtain ⟨d,hd,hm,hp⟩ := sourceKPAdelicCuspFrequencyPeriod_common K hζ (m:K) g
  obtain ⟨c,hc,hmap⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ d hd
  let B := sourceKPCuspHeightBox K
  let hB := sourceKPCuspHeightBox_isCompact K
  let hbpos := sourceKPCuspHeightBox_positive K
  let F := sourceKPCuspNativeFourierTest K hζ d hd Q B hB hbpos (m:K) hT
  let G := fun s => ψ[m, u] * sourceKPCuspNativeFourierTest K hζ d hd qf B hB hbpos (m:K) hT s
  let D : Set ℂ := {s | 0 < s.re}
  have hD : IsPreconnected D :=
    ((convex_Ioi (𝕜 := ℝ) (0:ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have hF : MeromorphicOn F D :=
    sourceKPCuspNativeFourierTest_meromorphic K hζ d hd Q B hB hbpos (m:K) hT
  have hG : MeromorphicOn G D := fun s hs =>
    (show AnalyticAt ℂ (fun _ : ℂ => ψ[m, u]) s from analyticAt_const).meromorphicAt.mul
      (sourceKPCuspNativeFourierTest_meromorphic K hζ d hd qf B hB hbpos (m:K) hT s hs)
  let b : ℝ := ((3*(Module.finrank ℚ K+1):ℕ):ℝ)
  let a : ℂ := b
  have hb : 0 < b := by dsimp only [b]; positivity
  have ha : a ∈ D := by change 0 < a.re; simpa only [a,Complex.ofReal_re] using hb
  have hab : b/2 < a.re := by simp only [a,Complex.ofReal_re]; linarith
  have hinit : F =ᶠ[𝓝 a] G := by
    filter_upwards [(Complex.continuous_re.tendsto a).eventually (Ioi_mem_nhds hab)] with s hs
    have hs' : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1 := by
      change b ≤ 2*s.re+1
      linarith
    exact sourceKPCuspNativeFourierTest_left_finite_upper_initial K hζ m qf u d hd hm
      (hp false) (hp true) c hc hmap B hB hbpos hT hs'
  have heq := sourceKPMeromorphicOn_eventuallyEq_of_germ hF hG hD ha
    (show (1/6:ℂ) ∈ D by change 0 < (1/6:ℂ).re; norm_num) hinit
  let res (v : Gf) := sourceKPCuspNativeFourierResidue K hζ d hd v B hB hbpos (m:K) hT
  have hleft : Tendsto (fun s => (s-1/6)*F s) (𝓝[≠] (1/6:ℂ)) (𝓝 (res Q)) :=
    sourceKPCuspNativeFourierTest_residue_tendsto K hζ d hd Q B hB hbpos (m:K) hT
  have hright : Tendsto (fun s => (s-1/6)*G s) (𝓝[≠] (1/6:ℂ)) (𝓝 (ψ[m, u] * res qf)) := by
    have h := sourceKPCuspNativeFourierTest_residue_tendsto K hζ d hd qf B hB hbpos (m:K) hT
    have hcst : Tendsto (fun _ : ℂ => ψ[m, u]) (𝓝[≠] (1/6:ℂ)) (𝓝 (ψ[m, u])) :=
      tendsto_const_nhds
    apply (hcst.mul h).congr'
    filter_upwards with s
    exact mul_left_comm _ _ _
  have hres : res Q = ψ[m, u] * res qf := by
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [heq] with s hs
    exact congrArg (fun w : ℂ => (s-1/6)*w) hs.symm
  rw [sourceKPCuspResidualFourierValue_eq_coefficient K hζ m hT Q d hd c hc (hp true) hm hmap,
    sourceKPCuspResidualFourierValue_eq_coefficient K hζ m hT qf d hd c hc (hp false) hm hmap]
  change res Q / ((c:ℂ)*sourceKPCuspArchFourierMoment K hζ m B (1/6)) =
    ψ[m, u] * (res qf / ((c:ℂ)*sourceKPCuspArchFourierMoment K hζ m B (1/6)))
  rw [hres, mul_div_assoc]

end
end ArtinMatthews
