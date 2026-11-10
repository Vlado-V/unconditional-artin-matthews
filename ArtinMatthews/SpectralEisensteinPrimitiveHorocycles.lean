module

public import ArtinMatthews.SpectralHorizontalPeriodPartition
public import ArtinMatthews.SpectralCuspTrueWidth
public import ArtinMatthews.SpectralGamma0EisensteinIntegralExchange
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.SpectralEisensteinEquivalentMeans
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual primitive horizontal period and its compact partition.
The period integral is computed at true width; the common-N mean is the
same mean with its exact width factor retained. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem spectralHorizontalPartition_period_integral {w : ℝ} (hw : 0<w)
    (F : ℝ → ℂ) (hF : Continuous F) (hp : Function.Periodic F w) :
    (∫ x in (0:ℝ)..2*w, (spectralHorizontalPartition w x:ℂ)*F x)=∫ x in (0:ℝ)..w,F x := by
  let G (x : ℝ) := (spectralHorizontalPartition w x:ℂ)*F x
  have hG : Continuous G :=
    (Complex.continuous_ofReal.comp (spectralHorizontalPartition_contDiff w).continuous).mul hF
  have hshift : (∫ x in (0:ℝ)..w, G (x+w))=∫ x in w..2*w,G x := by
    rw [intervalIntegral.integral_comp_add_right,zero_add,two_mul]
  change (∫ x in (0:ℝ)..2*w, G x)=_
  calc
    _=(∫ x in (0:ℝ)..w,G x)+(∫ x in w..2*w,G x) :=
      (intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable _ _)
        (hG.intervalIntegrable _ _)).symm
    _=∫ x in (0:ℝ)..w,G x+G (x+w) := by
      have hG' : Continuous (fun x : ℝ => G (x+w)) :=
        hG.comp (continuous_id.add continuous_const)
      rw [intervalIntegral.integral_add (hG.intervalIntegrable 0 w) (hG'.intervalIntegrable 0 w),hshift]
    _=_ := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x∈Icc 0 w := by simpa only [uIcc_of_le hw.le] using hx
      have hs := congrArg Complex.ofReal (spectralHorizontalPartition_add_shift hw hx')
      simp only [Complex.ofReal_add,Complex.ofReal_one] at hs
      simp only [G,hp x,← add_mul,hs,one_mul]

theorem gamma0Invariant_rawCusp_primitive_period (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ.val • z)=F z)
    (y : ℝ) (hy : 0<y) :
    Function.Periodic (fun x => F (r⁻¹ • gamma0EisensteinHorizontalPoint y hy x))
      (gamma0CuspTrueWidth N r:ℝ) := by
  intro x
  let k : ℤ := gamma0CuspTrueWidth N r
  let T := integerTranslation k
  let γ : CongruenceSubgroup.Gamma0 N := ⟨r⁻¹*T*r,
    (gamma0CuspTrueWidth_translation_iff N r k).mpr dvd_rfl⟩
  have hT : T • gamma0EisensteinHorizontalPoint y hy x=
      gamma0EisensteinHorizontalPoint y hy (x+(gamma0CuspTrueWidth N r:ℝ)) := by
    rw [specialLinear_upper_smul_horizontalPoint T (by simp [T,integerTranslation])]
    simp [T,k,integerTranslation]
  have hγ : γ.val*r⁻¹=r⁻¹*T := by dsimp [γ];group
  change F (r⁻¹ • gamma0EisensteinHorizontalPoint y hy (x+(gamma0CuspTrueWidth N r:ℝ)))=_
  rw [← hT,← mul_smul,← hγ,mul_smul,hF γ]

theorem gamma0Invariant_primitive_integral_eq_common_mean (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (F : UpperHalfPlane → ℂ) (hc : Continuous F)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ.val • z)=F z)
    (y : ℝ) (hy : 0<y) :
    (∫ x in (0:ℝ)..(gamma0CuspTrueWidth N r:ℝ), F (r⁻¹ • gamma0EisensteinHorizontalPoint y hy x))=
      (gamma0CuspTrueWidth N r:ℂ)*((N:ℂ)⁻¹*
        ∫ x in (0:ℝ)..(N:ℝ),F (r⁻¹ • gamma0EisensteinHorizontalPoint y hy x)) := by
  let w : ℝ := gamma0CuspTrueWidth N r
  let d := gamma0CuspFrequencyStep N r
  let G (x : ℝ) := F (r⁻¹ • gamma0EisensteinHorizontalPoint y hy x)
  have hG : Continuous G := hc.comp ((continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹)).comp
    (gamma0EisensteinHorizontalPoint_continuous y hy))
  have hN : (d:ℝ)*(gamma0CuspTrueWidth N r:ℝ)=(N:ℝ) := by
    rw [mul_comm]
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N r
  have hNc : (d:ℂ)*(w:ℂ)=(N:ℂ) := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_natCast,w] using congrArg Complex.ofReal hN
  have hp := gamma0Invariant_rawCusp_primitive_period N r F hF y hy
  have hi := hp.intervalIntegral_add_zsmul_eq (d:ℤ) 0 (fun x z => hG.intervalIntegrable x z)
  have he : (∫ x in (0:ℝ)..(N:ℝ),G x)=(d:ℂ)*(∫ x in (0:ℝ)..w,G x) := by
    simpa only [zero_add,zsmul_eq_mul,Int.cast_natCast,hN] using hi
  change (∫ x in (0:ℝ)..w,G x)=(w:ℂ)*((N:ℂ)⁻¹*(∫ x in (0:ℝ)..(N:ℝ),G x))
  rw [he]
  field_simp [show (N:ℂ)≠0 by exact_mod_cast NeZero.ne N]
  rw [← hNc]
  ring

end ArtinMatthews
