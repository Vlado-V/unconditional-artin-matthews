module

public import ArtinMatthews.SpectralCuspBesselTransform
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! Weight-zero source convention. ABL Section 3.2 adopts Drappeau
Section 4.1.2, where the Fourier wave is W_(0,it)(4*pi*|n|*y).
DLMF 13.18.9 specifies W_(0,nu)(x)=sqrt(x/pi)*K_nu(x/2).
The K function here is the existing Schlaefli integral. -/

noncomputable section
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralABLWhittakerZero (ν : ℂ) (x : ℝ) : ℂ :=
  (Real.sqrt (x/Real.pi) : ℂ)*schlafliBesselK ν (x/2)

theorem spectralABLWhittakerZero_fourier (ν : ℂ) (q y : ℝ) (hq : 0 < q) (_hy : 0 < y) :
    spectralABLWhittakerZero ν (4*Real.pi*q*y) =
      (2*Real.sqrt q : ℂ)*cuspBesselKernel ν (2*Real.pi*q) y := by
  unfold spectralABLWhittakerZero cuspBesselKernel
  have hs : 4*Real.pi*q*y/Real.pi = 4*(q*y) := by field_simp
  rw [hs,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),Real.sqrt_mul hq.le]
  rw [show Real.sqrt (4 : ℝ) = 2 by norm_num]
  push_cast
  rw [show 4*Real.pi*q*y/2 = 2*Real.pi*q*y by ring]
  ring

def spectralABLRhoFromNative (w q : ℝ) (A : ℂ) : ℂ :=
  ((Real.sqrt w/(2*Real.sqrt q) : ℝ) : ℂ)*A

theorem spectralABLRhoFromNative_scale (w q : ℝ) (hq : 0 < q) (A : ℂ) :
    (2*Real.sqrt q : ℂ)*spectralABLRhoFromNative w q A = (Real.sqrt w : ℂ)*A := by
  unfold spectralABLRhoFromNative
  push_cast
  field_simp [(Real.sqrt_pos.mpr hq).ne']

theorem spectralABLRhoFromNative_reconstruction (ν A : ℂ) (w q y : ℝ)
    (hw : 0 < w) (hq : 0 < q) (hy : 0 < y) :
    A*cuspBesselKernel ν (2*Real.pi*q/w) y =
      spectralABLRhoFromNative w q A*spectralABLWhittakerZero ν (4*Real.pi*q*y/w) := by
  have harg : 4*Real.pi*q*y/w = 4*Real.pi*(q/w)*y := by ring
  rw [harg,spectralABLWhittakerZero_fourier ν (q/w) y (div_pos hq hw) hy]
  unfold spectralABLRhoFromNative
  rw [Real.sqrt_div hq.le]
  push_cast
  have hw0 : (Real.sqrt w : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hw).ne'
  have hq0 : (Real.sqrt q : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  rw [show 2*Real.pi*(q/w) = 2*Real.pi*q/w by ring]
  field_simp

theorem spectralABLRhoFromNative_norm_sq (w q : ℝ) (hw : 0 < w) (hq : 0 < q) (A : ℂ) :
    ‖spectralABLRhoFromNative w q A‖^2 = w/(4*q)*‖A‖^2 := by
  unfold spectralABLRhoFromNative
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity),mul_pow,div_pow,mul_pow,
    Real.sq_sqrt hw.le,Real.sq_sqrt hq.le]
  norm_num

theorem spectralABLRhoFromNative_weighted_norm_sq (w q h c : ℝ)
    (hw : 0 < w) (hq : 0 < q) (A : ℂ) :
    h*‖spectralABLRhoFromNative w q A‖^2/c =
      (h/c)*(w/(4*q))*‖A‖^2 := by
  rw [spectralABLRhoFromNative_norm_sq w q hw hq A]
  ring

end ArtinMatthews
