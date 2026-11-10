module

public import ArtinMatthews.SpectralBetaRational
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence and exact evaluation of the complex quadratic beta integral. -/
noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

def spectralQuadraticPower (s : ℂ) (x : ℝ) : ℂ := (1+(x:ℂ)^2)^(-s)

@[simp] theorem spectralQuadraticPower_neg (s : ℂ) (x : ℝ) :
    spectralQuadraticPower s (-x)=spectralQuadraticPower s x := by
  simp [spectralQuadraticPower]

theorem spectralQuadraticPower_mellin_integrand (s : ℂ) (t : ℝ) :
    spectralBetaRationalProfile (1/2) (s-1/2) t =
      (t:ℂ)^((1/2:ℂ)-1)*(1+(t:ℂ))^(-s) := by
  unfold spectralBetaRationalProfile
  congr 2
  ring

theorem spectralQuadraticPower_half_integrable (s : ℂ) (hs : 1/2<s.re) :
    IntegrableOn (spectralQuadraticPower s) (Ioi 0) := by
  have hb : 0<(s-1/2).re := by norm_num; linarith
  have hrat := spectralBetaRationalProfile_integrable (1/2) (s-1/2) (by norm_num) hb
  change IntegrableOn (fun t => spectralBetaRationalProfile (1/2) (s-1/2) t) (Ioi 0) at hrat
  have hmel : MellinConvergent (fun t : ℝ => (1+(t:ℂ))^(-s)) (1/2) := by
    simpa only [MellinConvergent,smul_eq_mul,spectralQuadraticPower_mellin_integrand] using hrat
  have h := (MellinConvergent.comp_rpow (f := fun t : ℝ => (1+(t:ℂ))^(-s))
    (s := 1) (a := 2) (by norm_num)).mpr hmel
  change IntegrableOn (fun x : ℝ => (1+(x:ℂ)^2)^(-s)) (Ioi 0)
  simpa only [MellinConvergent,sub_self,Complex.cpow_zero,one_smul,Real.rpow_two,
    Complex.ofReal_pow] using h

theorem spectralQuadraticPower_half_integral (s : ℂ) :
    (∫ x : ℝ in Ioi 0, spectralQuadraticPower s x) =
      (1/2:ℂ)*Complex.betaIntegral (1/2) (s-1/2) := by
  have h := mellin_comp_rpow (fun t : ℝ => (1+(t:ℂ))^(-s)) 1 2
  have he : mellin (fun t : ℝ => (1+(t:ℂ))^(-s)) (1/2) =
      Complex.betaIntegral (1/2) (s-1/2) := by
    simpa only [mellin,smul_eq_mul,spectralQuadraticPower_mellin_integrand] using
      spectralBetaRationalProfile_integral (1/2) (s-1/2)
  have h' : (∫ x : ℝ in Ioi 0, spectralQuadraticPower s x) =
      (1/2:ℂ)*mellin (fun t : ℝ => (1+(t:ℂ))^(-s)) (1/2) := by
    simpa [mellin,spectralQuadraticPower,Real.rpow_two] using h
  rw [he] at h'
  exact h'

theorem spectralQuadraticPower_integrable (s : ℂ) (hs : 1/2<s.re) :
    Integrable (spectralQuadraticPower s) := by
  have hp := spectralQuadraticPower_half_integrable s hs
  have hn : IntegrableOn (spectralQuadraticPower s) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def,neg_preimage,neg_Iic,neg_zero,spectralQuadraticPower_neg]
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact hp
  have hu := hn.union hp
  simpa only [Iic_union_Ioi,integrableOn_univ] using hu

theorem spectralQuadraticPower_integral_beta (s : ℂ) (hs : 1/2<s.re) :
    (∫ x : ℝ, spectralQuadraticPower s x) = Complex.betaIntegral (1/2) (s-1/2) := by
  have hi := spectralQuadraticPower_integrable s hs
  have he : (∫ x : ℝ in Iic 0, spectralQuadraticPower s x) =
      ∫ x : ℝ in Ioi 0, spectralQuadraticPower s x := by
    simpa only [neg_zero,spectralQuadraticPower_neg] using
      (integral_comp_neg_Ioi 0 (spectralQuadraticPower s)).symm
  rw [← intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn,
    he,spectralQuadraticPower_half_integral]
  ring

theorem spectralQuadraticPower_integral (s : ℂ) (hs : 1/2<s.re) :
    (∫ x : ℝ, spectralQuadraticPower s x) =
      (Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s := by
  rw [spectralQuadraticPower_integral_beta s hs,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by simp; linarith),
    show (1/2:ℂ)+(s-1/2)=s by ring]
  have hg : Complex.Gamma (1/2)= (Real.sqrt Real.pi:ℂ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
      (Complex.Gamma_ofReal (1/2)).trans (congrArg (fun x : ℝ => (x:ℂ)) Real.Gamma_one_half_eq)
  rw [hg]

end ArtinMatthews
