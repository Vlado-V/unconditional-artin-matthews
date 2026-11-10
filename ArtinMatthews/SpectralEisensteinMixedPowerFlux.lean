module

public import ArtinMatthews.SpectralEisensteinTruncatedPairFlux
public import ArtinMatthews.SpectralEisensteinCriticalPowerFlux
public import ArtinMatthews.SpectralEisensteinCutoffConjugation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The mixed upper-band Green flux pairs the reflected outgoing
coefficient with the incoming coefficient. The other mixed term
cancels by exact conjugation of the actual cutoff and its error. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

theorem spectralRadialInner_intervalIntegrable (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    {L U : ℝ} (hL : 0<L) (hLU : L≤U) :
    IntervalIntegrable (fun t => ((t^2:ℝ)⁻¹) • inner ℂ (f t) (g t)) volume L U := by
  have hw : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (uIcc L U) :=
    (continuous_id.pow 2).continuousOn.inv₀ (fun t ht =>
      pow_ne_zero 2 (hL.trans_le ((uIcc_of_le hLU ▸ ht).1)).ne')
  exact (hw.smul (hf.inner hg).continuousOn).intervalIntegrable

theorem eisensteinCriticalTruncatedPair_mixed_upper_band_flux {s : ℂ} (hs : s.re=1/2)
    {A : ℝ} (hA : 0<A) (hA2 : A<1/2) (B c d : ℂ) :
    (∫ t in (1/A)..(2/A), ((t^2:ℝ)⁻¹) •
      inner ℂ (B*eisensteinUpperCutoffError s A t) (eisensteinCriticalTruncatedPair s A c d t))-
    (∫ t in (1/A)..(2/A), ((t^2:ℝ)⁻¹) •
      inner ℂ (B*eisensteinOutgoingApprox s A t) (eisensteinCriticalUpperErrorPair s A c d t))=
      (2:ℂ)*(s.im:ℂ)*Complex.I*(starRingEnd ℂ) B*c := by
  let f := eisensteinOutgoingApprox s A
  let g := eisensteinUpperCutoffError s A
  let F := eisensteinCriticalTruncatedPair s A c d
  let G := eisensteinCriticalUpperErrorPair s A c d
  let K (t : ℝ) := ((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t)
  let L : ℝ := 1/A
  let U : ℝ := 2/A
  have hL : 0<L := one_div_pos.mpr hA
  have hLU : L≤U := div_le_div_of_nonneg_right (by norm_num) hA.le
  have hf : Continuous f := (eisensteinOutgoingApprox_smooth s A).continuous
  have hg : Continuous g := (eisensteinUpperCutoffError_smooth s A).continuous
  have hF : Continuous F := (eisensteinCriticalTruncatedPair_smooth s A c d).continuous
  have hG : Continuous G := (eisensteinCriticalUpperErrorPair_smooth s A c d).continuous
  have hKi : IntervalIntegrable K volume L U := spectralRadialInner_intervalIntegrable g f hg hf hL hLU
  have hKc : IntervalIntegrable (fun t => (starRingEnd ℂ) (K t)) volume L U := by
    have hK : ContinuousOn K (uIcc L U) := by
      have hw : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (uIcc L U) :=
        (continuous_id.pow 2).continuousOn.inv₀ (fun t ht =>
          pow_ne_zero 2 (hL.trans_le ((uIcc_of_le hLU ▸ ht).1)).ne')
      exact hw.smul (hg.inner hf).continuousOn
    exact (Complex.conjLIE.continuous.comp_continuousOn hK).intervalIntegrable
  have hIm : (∫ t in L..U,K t).im=s.im := by
    simpa [K,L,U,eisensteinCriticalUpperErrorPair,eisensteinCriticalTruncatedPair] using
      eisensteinCriticalTruncatedPair_upper_band_flux hs hA hA2 1 0
  have hConj : (∫ t in L..U,(starRingEnd ℂ) (K t))=(starRingEnd ℂ) (∫ t in L..U,K t) :=
    Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm K
  have hDiff : (∫ t in L..U,K t)-(starRingEnd ℂ) (∫ t in L..U,K t)=(2:ℂ)*(s.im:ℂ)*Complex.I := by
    apply Complex.ext
    · simp [Complex.mul_re,Complex.mul_im]
    · simp [Complex.mul_re,Complex.mul_im,hIm]
      ring
  change (∫ t in L..U,((t^2:ℝ)⁻¹) • inner ℂ (B*g t) (F t))-
    (∫ t in L..U,((t^2:ℝ)⁻¹) • inner ℂ (B*f t) (G t))=_
  have hFi : IntervalIntegrable (fun t => ((t^2:ℝ)⁻¹) • inner ℂ (B*g t) (F t)) volume L U :=
    spectralRadialInner_intervalIntegrable (fun t => B*g t) F (continuous_const.mul hg) hF hL hLU
  have hGi : IntervalIntegrable (fun t => ((t^2:ℝ)⁻¹) • inner ℂ (B*f t) (G t)) volume L U :=
    spectralRadialInner_intervalIntegrable (fun t => B*f t) G (continuous_const.mul hf) hG hL hLU
  rw [← intervalIntegral.integral_sub hFi hGi]
  calc
    _ = ∫ t in L..U, ((starRingEnd ℂ) B*c)*(K t-(starRingEnd ℂ) (K t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 : 0<t := hL.trans_le ((uIcc_of_le hLU ▸ ht).1)
      change ((t^2:ℝ)⁻¹) • inner ℂ (B*g t) (F t)-
        ((t^2:ℝ)⁻¹) • inner ℂ (B*f t) (G t)=_
      simp only [F,G,f,g,K,eisensteinCriticalTruncatedPair,eisensteinCriticalUpperErrorPair,
        eisensteinCriticalParameter_conj hs,eisensteinOutgoingApprox_conj s A ht0.le,
        eisensteinUpperCutoffError_conj s hA.le,RCLike.inner_apply,map_mul,starRingEnd_self_apply,
        Complex.real_smul,Complex.conj_ofReal]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub hKi hKc,hConj,hDiff]
      ring

end ArtinMatthews
