module

public import ArtinMatthews.SpectralEisensteinGreenMultiplier
public import ArtinMatthews.SpectralEisensteinCriticalTests
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Literal moments of the bounded Green multiplier on the Eisenstein
coefficient space, with its normalized positive-frequency measure. -/
noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

theorem gamma0EisensteinGreenScalarOperator_power_ae
    (f : Lp ℂ 2 gamma0EisensteinSpectralMeasure) (n : ℕ) :
    ((gamma0EisensteinGreenScalarOperator^n) f)=ᵐ[gamma0EisensteinSpectralMeasure]
      fun t => gamma0EisensteinGreenWeight t^n*f t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := gamma0EisensteinGreenMultiply_ae ((gamma0EisensteinGreenScalarOperator^n) f)
    rw [pow_succ',mul_apply_eq_comp]
    filter_upwards [h,ih] with t ht hn
    change gamma0EisensteinGreenMultiply ((gamma0EisensteinGreenScalarOperator^n) f) t=_
    rw [ht,hn,pow_succ']
    ring

theorem gamma0EisensteinGreenMultiplier_power_apply (N : ℕ) [NeZero N]
    (f : Gamma0EisensteinSpectralSpace N) (n : ℕ) (i : Gamma0EisensteinCuspClasses N) :
    ((gamma0EisensteinGreenMultiplier N)^n) f i=
      (gamma0EisensteinGreenScalarOperator^n) (f i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ',mul_apply_eq_comp,mul_apply_eq_comp,gamma0EisensteinGreenMultiplier_apply,ih]
    rfl

theorem gamma0EisensteinGreenMoment_integrableOn (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (i : Gamma0EisensteinCuspClasses N) (n : ℕ) :
    IntegrableOn (fun t => ((‖gamma0StoneEisensteinAmplitude N ψ i t‖^2:ℝ):ℂ)*
      gamma0EisensteinGreenWeight t^n) (Ioi 0) := by
  have hm : AEStronglyMeasurable (fun t => ((‖gamma0StoneEisensteinAmplitude N ψ i t‖^2:ℝ):ℂ)*
      gamma0EisensteinGreenWeight t^n) (volume.restrict (Ioi 0)) :=
    ((Complex.measurable_ofReal.comp ((gamma0StoneEisensteinAmplitude_measurable N ψ i).norm.pow_const 2)).mul
      (gamma0EisensteinGreenWeight_measurable.pow_const n)).aestronglyMeasurable
  apply (gamma0StoneEisensteinAmplitude_sq_integrableOn N ψ i).mono' hm
  exact ae_of_all _ (fun t => by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _),norm_pow]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) (gamma0EisensteinGreenWeight_norm_le t))
      (sq_nonneg _)).trans_eq (mul_one _))

theorem gamma0EisensteinCoefficient_green_moment (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (i : Gamma0EisensteinCuspClasses N) (n : ℕ) :
    inner ℂ (gamma0EisensteinCoefficientLp N i ψ)
      ((gamma0EisensteinGreenScalarOperator^n) (gamma0EisensteinCoefficientLp N i ψ))=
      (((2*Real.pi)⁻¹:ℝ):ℂ)*(∫ t in Ioi 0,
        ((‖gamma0StoneEisensteinAmplitude N ψ i t‖^2:ℝ):ℂ)*gamma0EisensteinGreenWeight t^n) := by
  let f := gamma0EisensteinCoefficientLp N i ψ
  calc
    inner ℂ f ((gamma0EisensteinGreenScalarOperator^n) f)=
        ∫ t,((‖gamma0StoneEisensteinAmplitude N ψ i t‖^2:ℝ):ℂ)*gamma0EisensteinGreenWeight t^n
          ∂gamma0EisensteinSpectralMeasure := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [gamma0EisensteinCoefficientLp_ae N i ψ,
        gamma0EisensteinGreenScalarOperator_power_ae f n] with t hf hp
      change inner ℂ (f t) (((gamma0EisensteinGreenScalarOperator^n) f) t)=_
      rw [hp]
      rw [RCLike.inner_apply,hf,show (starRingEnd ℂ) ((starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ψ i t))=
        gamma0StoneEisensteinAmplitude N ψ i t from star_star _]
      calc
        _ = ((starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ψ i t)*
          gamma0StoneEisensteinAmplitude N ψ i t)*gamma0EisensteinGreenWeight t^n := by ring
        _ = _ := by rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    _ = _ := by
      have hc : 0≤(2*Real.pi)⁻¹ := inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le)
      rw [gamma0EisensteinSpectralMeasure,integral_smul_measure,ENNReal.toReal_ofReal hc,Complex.real_smul]

theorem gamma0EisensteinSeedAnalysis_green_moment (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (n : ℕ) :
    inner ℂ (gamma0EisensteinSeedAnalysis N ψ)
      (((gamma0EisensteinGreenMultiplier N)^n) (gamma0EisensteinSeedAnalysis N ψ))=
      ∫ t in Ioi 0,(gamma0StoneFrequencyDensity N ψ t:ℂ)*gamma0EisensteinGreenWeight t^n := by
  change (∑ i,inner ℂ (gamma0EisensteinSeedAnalysis N ψ i)
    ((((gamma0EisensteinGreenMultiplier N)^n) (gamma0EisensteinSeedAnalysis N ψ)) i))=_
  simp_rw [gamma0EisensteinGreenMultiplier_power_apply,gamma0EisensteinSeedAnalysis_apply,
    gamma0EisensteinCoefficient_green_moment]
  rw [← Finset.mul_sum,← integral_finsetSum Finset.univ
    (fun i _ => gamma0EisensteinGreenMoment_integrableOn N ψ i n),← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    change (((2*Real.pi)⁻¹:ℝ):ℂ)*(∑ i,((‖gamma0StoneEisensteinAmplitude N ψ i t‖^2:ℝ):ℂ)*
      gamma0EisensteinGreenWeight t^n)=_
    rw [← Finset.sum_mul]
    change (((2*Real.pi)⁻¹:ℝ):ℂ)*((∑ i,((‖gamma0StoneEisensteinAmplitude N ψ i t‖^2:ℝ):ℂ))*
      gamma0EisensteinGreenWeight t^n)=
        (((∑ i : Gamma0EisensteinCuspClasses N,‖gamma0StoneEisensteinAmplitude N ψ i t‖^2)/(2*Real.pi):ℝ):ℂ)*
          gamma0EisensteinGreenWeight t^n
    rw [Complex.ofReal_div,Complex.ofReal_sum,Complex.ofReal_inv]
    ring)

end ArtinMatthews
