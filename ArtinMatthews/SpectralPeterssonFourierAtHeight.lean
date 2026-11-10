module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.SpectralCuspTranslationAdmissibility
public import ArtinMatthews.SpectralHolomorphicCuspSeed
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.MathematicalPhysics.BFSS.RellichSmoothing


set_option backward.privateInPublic true
@[expose] public section

/-! Exact coefficient extraction on one normalized horizontal period,
including the exponential height correction in the holomorphic Fourier
coefficient. -/

noncomputable section
open MeasureTheory Set
open scoped Interval

namespace ArtinMatthews

def spectralPeterssonHeightPoint (x y : ℝ) (hy : 0 < y) : UpperHalfPlane :=
  ⟨⟨x,y⟩,hy⟩

theorem spectralPeterssonHeightPoint_coe (x y : ℝ) (hy : 0 < y) :
    ((spectralPeterssonHeightPoint x y hy : UpperHalfPlane) : ℂ) =
      (x : ℂ)+(y : ℂ)*Complex.I := by
  apply Complex.ext <;> simp [spectralPeterssonHeightPoint,Complex.mul_re,Complex.mul_im]

def spectralPeterssonQ (z : UpperHalfPlane) : ℂ :=
  Complex.exp (2*(Real.pi : ℂ)*Complex.I*(z : ℂ))

def spectralPeterssonFourierWeight (n : ℕ+) (z : UpperHalfPlane) : ℂ :=
  Complex.exp (-(2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(z : ℂ)))

def spectralPeterssonFourierAtHeight (F : UpperHalfPlane → ℂ)
    (n : ℕ+) (y : ℝ) (hy : 0 < y) : ℂ :=
  ∫ x in Ioc (0 : ℝ) 1, F (spectralPeterssonHeightPoint x y hy)*
    spectralPeterssonFourierWeight n (spectralPeterssonHeightPoint x y hy)

theorem spectralPeterssonQ_norm (z : UpperHalfPlane) :
    ‖spectralPeterssonQ z‖ = Real.exp (-(2*Real.pi*z.im)) := by
  simpa only [spectralHolomorphicCuspSeed,Nat.cast_one,mul_one,spectralPeterssonQ] using
    spectralHolomorphicCuspSeed_norm 1 z

theorem spectralPeterssonFourierWeight_norm (n : ℕ+) (z : UpperHalfPlane) :
    ‖spectralPeterssonFourierWeight n z‖ = Real.exp (2*Real.pi*(n : ℝ)*z.im) := by
  rw [spectralPeterssonFourierWeight,Complex.norm_exp]
  congr 1
  simp [Complex.mul_re,Complex.mul_im]

theorem spectralPeterssonFourierAtHeight_mode (m n : ℕ+) (y : ℝ) (hy : 0 < y) :
    spectralPeterssonFourierAtHeight (fun z => spectralPeterssonQ z^(m : ℕ)) n y hy =
      if m = n then 1 else 0 := by
  let d : ℤ := ((m : ℕ) : ℤ)-((n : ℕ) : ℤ)
  let c : ℂ := 2*(Real.pi : ℂ)*Complex.I*(d : ℂ)
  have hphase (x : ℝ) :
      spectralPeterssonQ (spectralPeterssonHeightPoint x y hy)^(m : ℕ)*
        spectralPeterssonFourierWeight n (spectralPeterssonHeightPoint x y hy) =
      Complex.exp (c*(x : ℂ))*Complex.exp (c*((y : ℂ)*Complex.I)) := by
    unfold spectralPeterssonQ spectralPeterssonFourierWeight
    rw [← Complex.exp_nat_mul,← Complex.exp_add,← Complex.exp_add,
      spectralPeterssonHeightPoint_coe]
    congr 1
    dsimp only [c,d]
    push_cast
    ring
  unfold spectralPeterssonFourierAtHeight
  simp_rw [hphase]
  rw [integral_mul_const]
  by_cases h : m = n
  · have hd : d = 0 := by simp [d,h]
    simp [c,hd,h]
  · have hd : d ≠ 0 := by
      intro he
      have hh : ((m : ℕ) : ℤ) = ((n : ℕ) : ℤ) := sub_eq_zero.mp he
      exact h (Subtype.ext (Int.natCast_inj.mp hh))
    have hc : c ≠ 0 := by
      dsimp only [c]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hd)
    have he : Complex.exp c = 1 := by
      simpa only [c,atkinPhase,Complex.ofReal_intCast] using atkinPhase_int d
    rw [← intervalIntegral.integral_of_le zero_le_one,integral_exp_mul_complex hc]
    simp [he,h]

theorem spectralPeterssonFourierAtHeight_qExpansion (F : UpperHalfPlane → ℂ)
    (A : ℕ+ → ℂ) (n : ℕ+) (y : ℝ) (hy : 0 < y)
    (hA : Summable (fun j : ℕ+ => A j*spectralPeterssonQ (spectralPeterssonHeightPoint 0 y hy)^(j : ℕ)))
    (hF : ∀ x ∈ Ioc (0 : ℝ) 1, F (spectralPeterssonHeightPoint x y hy) =
      ∑' j : ℕ+, A j*spectralPeterssonQ (spectralPeterssonHeightPoint x y hy)^(j : ℕ)) :
    spectralPeterssonFourierAtHeight F n y hy = A n := by
  classical
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let z (x : ℝ) := spectralPeterssonHeightPoint x y hy
  let W (j : ℕ+) (x : ℝ) := A j*spectralPeterssonQ (z x)^(j : ℕ)*spectralPeterssonFourierWeight n (z x)
  have hcont (j : ℕ+) : Continuous (W j) := by
    dsimp only [W,z,spectralPeterssonQ,spectralPeterssonFourierWeight]
    simp_rw [spectralPeterssonHeightPoint_coe]
    fun_prop
  have hInt (j : ℕ+) : Integrable (W j) μ :=
    ((hcont j).integrableOn_Icc (μ := volume) (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self
  have hnorm (j : ℕ+) (x : ℝ) :
      ‖W j x‖ = ‖A j*spectralPeterssonQ (z 0)^(j : ℕ)‖*‖spectralPeterssonFourierWeight n (z 0)‖ := by
    dsimp only [W]
    simp only [norm_mul,norm_pow,spectralPeterssonQ_norm,spectralPeterssonFourierWeight_norm]
    rfl
  have hs : Summable (fun j : ℕ+ => ∫ x, ‖W j x‖ ∂μ) := by
    apply (hA.norm.mul_right ‖spectralPeterssonFourierWeight n (z 0)‖).congr
    intro j
    change ‖A j*spectralPeterssonQ (z 0)^(j : ℕ)‖*‖spectralPeterssonFourierWeight n (z 0)‖ = _
    simp_rw [hnorm]
    simp [μ]
  have hstep : (∫ x in Ioc (0 : ℝ) 1, F (z x)*spectralPeterssonFourierWeight n (z x)) =
      ∫ x, ∑' j, W j x ∂μ := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    change F (z x)*spectralPeterssonFourierWeight n (z x) = _
    rw [hF x hx,← tsum_mul_right]
  unfold spectralPeterssonFourierAtHeight
  change (∫ x in Ioc (0 : ℝ) 1, F (z x)*spectralPeterssonFourierWeight n (z x)) = _
  rw [hstep,← integral_tsum_of_summable_integral_norm hInt hs]
  calc
    _ = ∑' j : ℕ+, A j*(if j = n then 1 else 0) := by
      apply tsum_congr
      intro j
      have he :
          (∫ x, W j x ∂μ) =
            A j*spectralPeterssonFourierAtHeight (fun z => spectralPeterssonQ z^(j : ℕ)) n y hy := by
        dsimp only [W,spectralPeterssonFourierAtHeight,μ]
        simp_rw [mul_assoc,integral_const_mul]
        rfl
      rw [he,spectralPeterssonFourierAtHeight_mode]
    _ = _ := by simp [mul_ite]

end ArtinMatthews
