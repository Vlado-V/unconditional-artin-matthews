module

public import ArtinMatthews.SourceKPCuspFourierFactor
public import ArtinMatthews.SourceKPCuspUnitArchMoment
public import ArtinMatthews.SourceKPBandResidueTransfer
public import ArtinMatthews.SourceKPCuspFourierMomentParameter
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

/-! The actual residue has the same normalized Fourier coefficient in every
compact positive height band. All identities are obtained from the original
initial-region integral and meromorphic uniqueness. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory Filter SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
variable (qf : SourceKPFiniteAdeleProjective K hζ)
variable (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
  ∃ k : sourceKPFiniteDeepMatrixGroup K,
    (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
      sourceKPFiniteDeepCoverLift K hζ k)
variable (m : Kˣ) (hm : ∃ r : 𝓞 K, (m:K)*(d:K) = (r:K))

include hperiod hm in
theorem sourceKPCuspNativeFourierTest_cross_germ
    (B C : Set (InfinitePlace K → ℝ)) (hB : IsCompact B) (hC : IsCompact C)
    (hBpos : ∀ y ∈ B, ∀ v, 0 < y v) (hCpos : ∀ y ∈ C, ∀ v, 0 < y v)
    {T : ℝ} (hT : 1 ≤ T) {s : ℂ} (hs : 0 < s.re) :
    (fun z => sourceKPCuspNativeFourierTest K hζ d hd qf B hB hBpos (m:K) hT z *
      sourceKPCuspArchFourierMoment K hζ m C z) =ᶠ[𝓝[≠] s]
    (fun z => sourceKPCuspNativeFourierTest K hζ d hd qf C hC hCpos (m:K) hT z *
      sourceKPCuspArchFourierMoment K hζ m B z) := by
  let F := sourceKPCuspNativeFourierTest K hζ d hd qf B hB hBpos (m:K) hT
  let G := sourceKPCuspNativeFourierTest K hζ d hd qf C hC hCpos (m:K) hT
  let A := sourceKPCuspArchFourierMoment K hζ m B
  let D := sourceKPCuspArchFourierMoment K hζ m C
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsPreconnected U :=
    ((convex_Ioi (𝕜 := ℝ) (0:ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have hF : MeromorphicOn F U := sourceKPCuspNativeFourierTest_meromorphic K hζ d hd qf B hB hBpos (m:K) hT
  have hG : MeromorphicOn G U := sourceKPCuspNativeFourierTest_meromorphic K hζ d hd qf C hC hCpos (m:K) hT
  have hA := sourceKPCuspArchFourierMoment_analyticOnNhd K hζ d hd m B hB hBpos
  have hD := sourceKPCuspArchFourierMoment_analyticOnNhd K hζ d hd m C hC hCpos
  have hFD : MeromorphicOn (fun z => F z*D z) U :=
    fun z hz => (hF z hz).mul (hD z hz).meromorphicAt
  have hGA : MeromorphicOn (fun z => G z*A z) U :=
    fun z hz => (hG z hz).mul (hA z hz).meromorphicAt
  let b : ℝ := ((3*(Module.finrank ℚ K+1):ℕ):ℝ)
  let a : ℂ := b
  have hb : 0 < b := by dsimp only [b]; positivity
  have ha : a ∈ U := by change 0 < a.re; simpa only [a,Complex.ofReal_re] using hb
  have hab : b/2 < a.re := by simp only [a,Complex.ofReal_re]; linarith
  obtain ⟨c,hc,hfactor⟩ := sourceKPCuspNativeFourierTest_initial_factor K hζ d hd qf hperiod m hm
  have he : (fun z => F z*D z) =ᶠ[𝓝 a] (fun z => G z*A z) := by
    filter_upwards [(Complex.continuous_re.tendsto a).eventually (Ioi_mem_nhds hab)] with z hz
    have hz' : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*z.re+1 := by
      change b ≤ 2*z.re+1
      linarith
    dsimp only [F,G,A,D]
    rw [hfactor B hB hBpos T hT z hz',hfactor C hC hCpos T hT z hz']
    ring
  exact sourceKPMeromorphicOn_eventuallyEq_of_germ hFD hGA hU ha hs he

include hperiod hm in
theorem sourceKPCuspNativeFourierResidue_cross
    (B C : Set (InfinitePlace K → ℝ)) (hB : IsCompact B) (hC : IsCompact C)
    (hBpos : ∀ y ∈ B, ∀ v, 0 < y v) (hCpos : ∀ y ∈ C, ∀ v, 0 < y v)
    {T : ℝ} (hT : 1 ≤ T) :
    sourceKPCuspNativeFourierResidue K hζ d hd qf B hB hBpos (m:K) hT *
      sourceKPCuspArchFourierMoment K hζ m C (1/6) =
    sourceKPCuspNativeFourierResidue K hζ d hd qf C hC hCpos (m:K) hT *
      sourceKPCuspArchFourierMoment K hζ m B (1/6) := by
  have he := sourceKPCuspNativeFourierTest_cross_germ K hζ d hd qf hperiod m hm
    B C hB hC hBpos hCpos hT (s := (1/6:ℂ)) (by norm_num)
  have hA : Tendsto (sourceKPCuspArchFourierMoment K hζ m B) (𝓝[≠] (1/6:ℂ))
      (𝓝 (sourceKPCuspArchFourierMoment K hζ m B (1/6))) :=
    (sourceKPCuspArchFourierMoment_analyticOnNhd K hζ d hd m B hB hBpos
    (1/6) (by norm_num)).continuousAt.mono_left nhdsWithin_le_nhds
  have hC' : Tendsto (sourceKPCuspArchFourierMoment K hζ m C) (𝓝[≠] (1/6:ℂ))
      (𝓝 (sourceKPCuspArchFourierMoment K hζ m C (1/6))) :=
    (sourceKPCuspArchFourierMoment_analyticOnNhd K hζ d hd m C hC hCpos
    (1/6) (by norm_num)).continuousAt.mono_left nhdsWithin_le_nhds
  have hL := (sourceKPCuspNativeFourierTest_residue_tendsto K hζ d hd qf B hB hBpos (m:K) hT).mul hC'
  have hR := (sourceKPCuspNativeFourierTest_residue_tendsto K hζ d hd qf C hC hCpos (m:K) hT).mul hA
  apply tendsto_nhds_unique hL
  apply hR.congr'
  filter_upwards [he] with z hz
  simpa only [mul_assoc] using congrArg (fun w : ℂ => (z-1/6)*w) hz.symm

include hperiod in
theorem sourceKPCuspNativeFourierResidue_unit_normalized
    (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
    (hBpos : ∀ y ∈ B, ∀ v, 0 < y v) {T : ℝ} (hT : 1 ≤ T) :
    sourceKPCuspNativeFourierResidue K hζ d hd qf B hB hBpos (1:K) hT =
      (sourceKPCuspNativeFourierResidue K hζ d hd qf (sourceKPCuspHeightBox K)
        (sourceKPCuspHeightBox_isCompact K) (sourceKPCuspHeightBox_positive K) (1:K) hT /
        sourceKPCuspUnitArchMoment K (1/6)) * sourceKPCuspArchFourierMoment K hζ (1:Kˣ) B (1/6) := by
  have hm' : ∃ r : 𝓞 K, ((1:Kˣ):K)*(d:K) = (r:K) := ⟨d,by simp⟩
  have h := sourceKPCuspNativeFourierResidue_cross K hζ d hd qf hperiod (1:Kˣ) hm'
    B (sourceKPCuspHeightBox K) hB (sourceKPCuspHeightBox_isCompact K)
    hBpos (sourceKPCuspHeightBox_positive K) hT
  rw [sourceKPCuspArchFourierMoment_unit_box] at h
  simp only [Units.val_one] at h
  have hn := sourceKPCuspUnitArchMoment_oneSixth_ne_zero K
  apply (mul_right_cancel₀ hn)
  calc
    _ = _ := h
    _ = _ := by field_simp [hn] <;> ring

end
end ArtinMatthews
