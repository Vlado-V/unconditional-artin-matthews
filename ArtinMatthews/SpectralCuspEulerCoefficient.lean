module

public import ArtinMatthews.SpectralCuspVerticalTesting
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.SpectralCuspComplexEulerEnergy
public import ArtinMatthews.SpectralCuspVerticalEnergy
public import ArtinMatthews.SpectralCuspWeightedGluingRepresentative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed genuine bounded L2 functional extracts the decaying Euler
coefficient. Its exact half-line moment avoids an unproved point trace. -/
noncomputable section
open Set MeasureTheory Filter
namespace ArtinMatthews

theorem cuspEulerCoefficientTest_memLp {w Y : ℝ} (hw : 0<w) (hY : 0<Y) :
    MemLp (fun y : ℝ => (y:ℂ)^(-1:ℂ)) 2
      ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) := by
  apply (memLp_two_iff_integrable_sq_norm (by
    simp only [Complex.cpow_neg_one]
    fun_prop)).mpr
  rw [cuspVerticalL2_integrable_density_iff hw hY]
  simpa only [one_mul] using cuspComplexEuler_power_energy_integrable (1:ℂ) hY
    (q:=(-1:ℂ)) (by norm_num)

def cuspEulerCoefficientTest {w Y : ℝ} (hw : 0<w) (hY : 0<Y) :
    CuspVerticalL2 w Y →L[ℂ] ℂ :=
  cuspVerticalL2Pairing (fun y : ℝ => (y:ℂ)^(-1:ℂ)) (cuspEulerCoefficientTest_memLp hw hY)

theorem cuspEulerCoefficientTest_power {w Y : ℝ} (hw : 0<w) (hY : 0<Y)
    (s B : ℂ) (hs : (1/2:ℝ)<s.re) (U : CuspVerticalL2 w Y)
    (hU : U =ᵐ[(cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y]
      fun y => B*(y:ℂ)^(1-s)) :
    cuspEulerCoefficientTest hw hY U=(w:ℂ)*B*(Y:ℂ)^(-s-1)/(s+1) := by
  rw [cuspEulerCoefficientTest,cuspVerticalL2Pairing_apply,
    cuspVerticalL2_integral_complex_density hw hY]
  have hUv := (spectralCuspVerticalL2_ae_iff hw hY).mp hU
  have hi : (∫ y in Ioi Y, (y^(-2:ℤ)) • (U y*(y:ℂ)^(-1:ℂ)))=
      B*(∫ y in Ioi Y, (y:ℂ)^(-s-2)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hUv,ae_restrict_mem measurableSet_Ioi] with y hy hyY
    have hn : (y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hY.trans hyY).ne'
    rw [hy]
    change (y^(-2:ℤ)) • (B*(y:ℂ)^(1-s)*(y:ℂ)^(-1:ℂ))=_
    have hp : (y:ℂ)^(-s-2)=(y:ℂ)^(1-s)/(y:ℂ)^3 := by
      rw [show -s-2=(1-s)-3 by ring,Complex.cpow_sub (1-s) 3 hn,Complex.cpow_ofNat]
    rw [hp]
    simp only [Complex.real_smul,zpow_neg,zpow_ofNat,Complex.ofReal_inv,
      Complex.ofReal_pow,Complex.cpow_neg_one]
    field_simp
  have hstrip : (-s-(2:ℂ)).re < -1 := by
    have hr : (-s-(2:ℂ)).re= -s.re-2 := by simp
    rw [hr]
    linarith
  rw [hi,integral_Ioi_cpow_of_lt hstrip hY]
  simp only [Complex.real_smul]
  have he : -s-2+1= -s-1 := by ring
  rw [he,show -s-1= -(s+1) by ring]
  simp only [div_neg,neg_div,neg_neg]
  ring

def cuspEulerCoefficientExtract {w Y : ℝ} (hw : 0<w) (hY : 0<Y) (s : ℂ) :
    CuspVerticalL2 w Y →L[ℂ] ℂ :=
  (((s+1)*(Y:ℂ)^(s+1)/(w:ℂ)):ℂ) • cuspEulerCoefficientTest hw hY

theorem cuspEulerCoefficientExtract_power {w Y : ℝ} (hw : 0<w) (hY : 0<Y)
    (s B : ℂ) (hs : (1/2:ℝ)<s.re) (U : CuspVerticalL2 w Y)
    (hU : U =ᵐ[(cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y]
      fun y => B*(y:ℂ)^(1-s)) : cuspEulerCoefficientExtract hw hY s U=B := by
  change ((s+1)*(Y:ℂ)^(s+1)/(w:ℂ))*cuspEulerCoefficientTest hw hY U=B
  rw [cuspEulerCoefficientTest_power hw hY s B hs U hU]
  have hwc : (w:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hw.ne'
  have hYc : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hs1 : s+1≠0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
    linarith
  have hp : (Y:ℂ)^(s+1)*(Y:ℂ)^(-s-1)=1 := by
    rw [← Complex.cpow_add _ _ hYc,show s+1+(-s-1)=0 by ring,Complex.cpow_zero]
  calc
    _=B*((Y:ℂ)^(s+1)*(Y:ℂ)^(-s-1)) := by field_simp
    _=B := by rw [hp,mul_one]

end ArtinMatthews
