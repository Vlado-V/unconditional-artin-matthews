module

public import ArtinMatthews.SourcePrincipalBallPrimalSupport
public import ArtinMatthews.SourcePrincipalBallFrequencyTransform
public import ArtinMatthews.StandardLocalFourier
public import ArtinMatthews.SourceFiniteBallIdealVolume
public import ArtinMatthews.StandardLocalHaarScaling
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The dual ball sum on the original frequency index, with the exact
finite Haar volume over the literal exterior ideal norm. -/
namespace ArtinMatthews.SourcePhysical

open NumberField NumberField.InfinitePlace IsDedekindDomain FractionalIdeal MeasureTheory
open VaryingKummerAnalytic SIntegerPrincipalization StandardAdelic
open scoped NumberField Classical nonZeroDivisors BigOperators SchwartzMap
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "FI" => FractionalIdeal (𝓞 K)⁰ K
local notation "S" => principalizingSet S₀
local notation "OS" => PrincipalIntegerRing S₀
local notation "d" => principalizingDenominator S₀
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

def sourcePrincipalBallFrequencySet (e : S → ℤ) (a : OS) : Set OS :=
  {h | ∀ v : S, algebraMap K (v.val.adicCompletion K) ((h : K) / (a : K)) ∈
    sourceLocalBall K v.val ((sourceDifferentExponent K v.val : ℤ) + e v)}

def sourcePrincipalBallDualTerm (e : S → ℤ) (a : OS) (ha : a ≠ 0)
    (w : OS ⧸ Ideal.span {a} → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) : OS → ℂ :=
  (sourcePrincipalBallFrequencySet K S₀ e a).indicator (fun h =>
    sourceNumberFieldComplexFourier K (sourceComplexTensor f)
      (sourceComplexFieldEmbedding K ((h : K) / (a : K))) *
      sourcePrincipalQuotientFourier K S₀ a ha w h)

theorem sourcePrincipalBallDualTerm_tsum (e : S → ℤ) (a : OS) (ha : a ≠ 0)
    (w : OS ⧸ Ideal.span {a} → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) :
    (∑' h, sourcePrincipalBallDualTerm K S₀ e a ha w f h) =
      ∑' h : SourcePrincipalBallFrequencies K S₀ e a,
        sourceNumberFieldComplexFourier K (sourceComplexTensor f)
          (sourceComplexFieldEmbedding K ((h.val : K) / (a : K))) *
          sourcePrincipalQuotientFourier K S₀ a ha w h.val := by
  unfold sourcePrincipalBallDualTerm
  rw [← tsum_subtype]
  rfl

def sourceFiniteBallVolume (e : S → ℤ) : ℝ :=
  ∏ v : S, (sourceLocalSelfDual K v.val).real (sourceLocalBall K v.val (-(e v)))

theorem sourcePrincipalBallCovolume_mul_finiteVolume (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hS : traceBadPlaces K ⊆ S) :
    sourcePrincipalBallCovolume K S₀ e M hM * sourceFiniteBallVolume K S₀ e = Ideal.absNorm M := by
  have hJ : 0 < (FractionalIdeal.absNorm (sourceFiniteBallIdeal K S e) : ℝ) := by
    rw [sourceFiniteBallIdeal_norm]
    exact Finset.prod_pos (fun v _ => zpow_pos (sourceLocalNorm_pos K v.val) _)
  have hD : 0 < Real.sqrt |(discr K : ℝ)| :=
    Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))
  unfold sourcePrincipalBallCovolume sourceFiniteBallVolume
  rw [sourcePrincipalBallProductUnit_val, map_mul, FractionalIdeal.coeIdeal_absNorm,
    Rat.cast_mul, Rat.cast_natCast, sourceFiniteBallIdeal_volume_product K S hS e]
  field_simp [hJ.ne', hD.ne']

variable [IsTotallyComplex K]

theorem sourcePrincipalBallDualTerm_summable_norm (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d})) (hS : traceBadPlaces K ⊆ S)
    (a : OS) (ha : a ≠ 0) (hgen : M.map (algebraMap (𝓞 K) OS) = Ideal.span {a})
    (hv : ∀ P : HeightOneSpectrum (𝓞 K), P ∉ S →
      P.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K P (M : FI)))
    (w : OS ⧸ Ideal.span {a} → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) :
    Summable (fun h => ‖sourcePrincipalBallDualTerm K S₀ e a ha w f h‖) := by
  let D := sourcePrincipalBallDualFrequencyEquiv K S₀ e M hM hc hS a ha hv
  have h := (sourcePrincipalBallDualWeighted_summable_norm K S₀ e M hM hc
    (fun q => w (Ideal.quotEquivOfEq hgen q)) f).comp_injective D.symm.injective
  unfold sourcePrincipalBallDualTerm
  simp_rw [norm_indicator_eq_indicator_norm]
  apply summable_subtype_iff_indicator.mp
  refine h.congr (fun x => ?_)
  change ‖_ * sourcePrincipalBallDualCoefficient K S₀ e M hc (fun q => w (Ideal.quotEquivOfEq hgen q))
      (((x.val : OS) : K) / (a : K))‖ = _
  rw [sourcePrincipalBallDualCoefficient_transform K S₀ e M hc a ha hgen w]
  rfl

theorem sourcePrincipalBallSupportedPoisson (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d})) (hS : traceBadPlaces K ⊆ S)
    (a : OS) (ha : a ≠ 0) (hgen : M.map (algebraMap (𝓞 K) OS) = Ideal.span {a})
    (hv : ∀ P : HeightOneSpectrum (𝓞 K), P ∉ S →
      P.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K P (M : FI)))
    (w : OS ⧸ Ideal.span {a} → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) :
    (∑' x, sourcePrincipalBallPrimalTerm K S₀ e a w f x) =
      ((sourceFiniteBallVolume K S₀ e : ℂ) / (Ideal.absNorm M : ℂ)) *
        ∑' h, sourcePrincipalBallDualTerm K S₀ e a ha w f h := by
  let C : ℂ := (sourcePrincipalBallCovolume K S₀ e M hM : ℂ)
  let V : ℂ := (sourceFiniteBallVolume K S₀ e : ℂ)
  let Q : ℂ := (Ideal.absNorm M : ℂ)
  let L := ∑' x, sourcePrincipalBallPrimalTerm K S₀ e a w f x
  let R := ∑' h, sourcePrincipalBallDualTerm K S₀ e a ha w f h
  have hP : C * L = R := by
    change _ * (∑' x, sourcePrincipalBallPrimalTerm K S₀ e a w f x) =
      ∑' h, sourcePrincipalBallDualTerm K S₀ e a ha w f h
    rw [sourcePrincipalBallPrimalTerm_tsum K S₀ e M a hgen w f, sourcePrincipalBallDualTerm_tsum]
    exact sourcePrincipalBallPeriodicPoisson_frequency K S₀ e M hM hc hS a ha hgen hv w f
  have hCV : C * V = Q := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using
      congrArg Complex.ofReal (sourcePrincipalBallCovolume_mul_finiteVolume K S₀ e M hM hS)
  have hQ : Q ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hM)
  change L = (V / Q) * R
  calc
    L = Q⁻¹ * (Q * L) := (inv_mul_cancel_left₀ hQ L).symm
    _ = (V / Q) * (C * L) := by rw [← hCV, div_eq_mul_inv]; ring
    _ = (V / Q) * R := by rw [hP]

end
end ArtinMatthews.SourcePhysical
