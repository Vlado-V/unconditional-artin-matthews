module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralQuadraticBetaIntegral
public import ArtinMatthews.SpectralQuadraticLineIntegral
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute dimensional reduction of the real-line quadratic Fourier
integral to the actual complex-plane source kernel. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralRealFourierPhase (b x : ℝ) : ℂ :=
  Complex.exp (-((2*Real.pi*b*x : ℝ) : ℂ)*Complex.I)

theorem spectralRealFourierPhase_norm (b x : ℝ) :
    ‖spectralRealFourierPhase b x‖ = 1 := by
  rw [spectralRealFourierPhase,Complex.norm_exp]
  simp

theorem spectralRealFourierPhase_breve (b x y : ℝ) :
    OAI.ShortDraftTrace.breveE (-((b/2 : ℝ) : ℂ)*Complex.mk x y) =
      spectralRealFourierPhase b x := by
  change Complex.exp (2*Real.pi*Complex.I*
    (-((b/2 : ℝ) : ℂ)*Complex.mk x y+
      (starRingEnd ℂ) (-((b/2 : ℝ) : ℂ)*Complex.mk x y))) = _
  unfold spectralRealFourierPhase
  congr 1
  apply Complex.ext
  · simp [Complex.mul_re,Complex.mul_im,Complex.conj_ofNat]
  · simp [Complex.mul_re,Complex.mul_im,Complex.conj_ofNat]
    ring

def spectralQuadraticFourier (s : ℂ) (b : ℝ) : ℂ :=
  ∫ x : ℝ, spectralQuadraticPower s x*spectralRealFourierPhase b x

theorem spectralQuadraticFourier_integrable (s : ℂ) (hs : 1/2 < s.re) (b : ℝ) :
    Integrable (fun x : ℝ => spectralQuadraticPower s x*spectralRealFourierPhase b x) := by
  apply (spectralQuadraticPower_integrable s hs).norm.mono'
  · unfold spectralQuadraticPower spectralRealFourierPhase
    fun_prop
  · exact ae_of_all _ fun x => by rw [norm_mul,spectralRealFourierPhase_norm,mul_one]

theorem spectralQuadraticFourier_dimensional_reduction (s : ℂ) (hs : 1/2 < s.re) (b : ℝ) :
    ((Real.sqrt Real.pi : ℂ)*Complex.Gamma s/Complex.Gamma (s+1/2)) *
      spectralQuadraticFourier s b =
        sourceFourierKernel (s+1/2) ((b/2 : ℝ) : ℂ) := by
  let S : ℂ := s+1/2
  let F (z : ℂ) := hyperbolicKernel S z*OAI.ShortDraftTrace.breveE (-((b/2 : ℝ) : ℂ)*z)
  let P (p : ℝ × ℝ) := F (Complex.measurableEquivRealProd.symm p)
  have hS : 1 < S.re := by dsimp only [S]; simp only [Complex.add_re]; norm_num; linarith
  have hF : Integrable F := sourceFourierKernel_integrable S _ hS
  have hmp : MeasurePreserving Complex.measurableEquivRealProd.symm volume volume :=
    MeasurePreserving.symm Complex.measurableEquivRealProd Complex.volume_preserving_equiv_real_prod
  have hP : Integrable P (volume.prod volume) :=
    (hmp.integrable_comp_emb Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr hF
  have hPxy (x y : ℝ) : P (x,y) =
      ((1+x^2+y^2 : ℝ) : ℂ)^(-S)*spectralRealFourierPhase b x := by
    dsimp only [P,F]
    rw [Complex.measurableEquivRealProd_symm_apply,spectralRealFourierPhase_breve]
    congr 1
    unfold hyperbolicKernel
    congr 1
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,add_assoc,pow_two]
  have hSlice (x : ℝ) : (∫ y : ℝ,P (x,y)) =
      ((Real.sqrt Real.pi : ℂ)*Complex.Gamma s/Complex.Gamma (s+1/2)) *
        (spectralQuadraticPower s x*spectralRealFourierPhase b x) := by
    simp_rw [hPxy]
    rw [integral_mul_const,spectralQuadraticLine_integral S (by linarith [hS]) (by positivity)]
    rw [show (1/2 : ℂ)-S = -s by dsimp [S];ring,
      show S-1/2=s by dsimp [S];ring]
    change (((1+x^2 : ℝ) : ℂ)^(-s)*
      ((Real.sqrt Real.pi : ℂ)*Complex.Gamma s/Complex.Gamma (s+1/2)))*
        spectralRealFourierPhase b x = _
    unfold spectralQuadraticPower
    push_cast
    ring
  have hIntegral : (∫ p : ℝ × ℝ,P p) = sourceFourierKernel S ((b/2 : ℝ) : ℂ) :=
    hmp.integral_comp Complex.measurableEquivRealProd.symm.measurableEmbedding F
  rw [← hIntegral]
  change _ = ∫ p : ℝ × ℝ,P p ∂(volume.prod volume)
  rw [integral_prod P hP]
  simp_rw [hSlice]
  rw [integral_const_mul]
  rfl

end ArtinMatthews

