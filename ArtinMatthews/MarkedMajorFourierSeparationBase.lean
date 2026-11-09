module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Prod


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine planar Schwartz Fourier transform and the normalization
for the inverse kernel exp(i(v*zeta+s*z)). -/
namespace ArtinMatthews
open MeasureTheory Complex
open scoped FourierTransform SchwartzMap RealInnerProductSpace
noncomputable section

abbrev MarkedMajorFourierPlane := WithLp 2 (ℝ × ℝ)

def markedMajorPlaneEquiv : MarkedMajorFourierPlane ≃L[ℝ] (ℝ × ℝ) :=
  (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).toContinuousLinearEquiv

def markedMajorPlaneLift (g : SchwartzMap (ℝ × ℝ) ℂ) :
    SchwartzMap MarkedMajorFourierPlane ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ markedMajorPlaneEquiv g

def markedMajorPlaneFourier (g : SchwartzMap (ℝ × ℝ) ℂ) :
    SchwartzMap (ℝ × ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ markedMajorPlaneEquiv.symm
    (𝓕 (markedMajorPlaneLift g))

def markedMajorFourierScale : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (LinearEquiv.smulOfNeZero ℝ (ℝ × ℝ) (2*Real.pi)⁻¹
    (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))).toContinuousLinearEquiv

/-- Actual Fourier coefficient, including the complete `(2*pi)^(-2)`
Jacobian for the positive exponential inversion convention. -/
def markedMajorFourierCoefficient (g : SchwartzMap (ℝ × ℝ) ℂ) :
    SchwartzMap (ℝ × ℝ) ℂ :=
  (((2*Real.pi)^2)⁻¹ : ℝ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ markedMajorFourierScale
      (markedMajorPlaneFourier g)

theorem markedMajorFourierScale_apply (p : ℝ × ℝ) :
    markedMajorFourierScale p = (p.1/(2*Real.pi),p.2/(2*Real.pi)) := by
  change ((2*Real.pi)⁻¹*p.1,(2*Real.pi)⁻¹*p.2) = _
  simp only [div_eq_mul_inv,mul_comm]

theorem markedMajorFourierCoefficient_apply (g : SchwartzMap (ℝ × ℝ) ℂ) (p : ℝ × ℝ) :
    markedMajorFourierCoefficient g p =
      ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ)*
        markedMajorPlaneFourier g (p.1/(2*Real.pi),p.2/(2*Real.pi)) := by
  change (((2*Real.pi)^2)⁻¹ : ℝ) • markedMajorPlaneFourier g (markedMajorFourierScale p) = _
  rw [markedMajorFourierScale_apply,Complex.real_smul]

theorem markedMajorPlaneFourier_inverse (g : SchwartzMap (ℝ × ℝ) ℂ) (x : ℝ × ℝ) :
    g x = ∫ p : ℝ × ℝ, Complex.exp (((2*Real.pi*(p.1*x.1+p.2*x.2) : ℝ) : ℂ)*I)*
      markedMajorPlaneFourier g p := by
  let G := markedMajorPlaneLift g
  have hinv := congrFun (G.continuous.fourierInv_fourier_eq G.integrable
    (𝓕 G).integrable) (WithLp.toLp 2 x)
  rw [Real.fourierInv_eq'] at hinv
  change (∫ p : MarkedMajorFourierPlane,
    Complex.exp (((2*Real.pi*inner ℝ p (WithLp.toLp 2 x) : ℝ) : ℂ)*I) • (𝓕 G) p) = g x at hinv
  have hmp := (WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
    (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding
    (fun p : MarkedMajorFourierPlane =>
      Complex.exp (((2*Real.pi*inner ℝ p (WithLp.toLp 2 x) : ℝ) : ℂ)*I) • (𝓕 G) p)
  rw [← hmp] at hinv
  change g x = ∫ p : ℝ × ℝ, Complex.exp (((2*Real.pi*(p.1*x.1+p.2*x.2) : ℝ) : ℂ)*I)*
    (𝓕 G) (WithLp.toLp 2 p)
  simpa [WithLp.prod_inner_apply,smul_eq_mul,mul_comm] using hinv.symm

end
end ArtinMatthews
