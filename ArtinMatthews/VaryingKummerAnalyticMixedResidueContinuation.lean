module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaContinuationBase
public import ArtinMatthews.VaryingKummerAnalyticMixedResidueTheta
public import ArtinMatthews.VaryingKummerAnalyticRayIdealCoefficients
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAnalytic
public import ArtinMatthews.VaryingKummerAnalyticMixedResidueMellin
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

/-! Genuine entire continuation of the residue-weighted ideal-class series
from its actual mixed-signature theta integral. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def mixedResidueIdealMellinFactor : ℂ :=
  (torsionOrder K : ℂ) * (mixedRadialJacobian K : ℂ)

theorem mixedResidueIdealMellinFactor_ne_zero : mixedResidueIdealMellinFactor K ≠ 0 :=
  mul_ne_zero (Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K))
    (Complex.ofReal_ne_zero.mpr (mixedRadialJacobian_pos K).ne')

def mixedResidueIdealContinued (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (s : ℂ) : ℂ :=
  (mixedResidueIdealMellinFactor K)⁻¹ * mixedInverseGammaFactor K s *
    ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val : ℝ) : ℂ)^s *
      mellin (fun t => ∫ u in mixedUnitLogDomain K, mixedIdealResidueFlowTheta K I hI N χ u t)
        ((Module.finrank ℚ K : ℂ)*s/2)

theorem mixedResidueIdealContinued_entire
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (hcop : IsCoprime I (rationalModulusIdeal (𝓞 K) N))
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1) :
    Differentiable ℂ (mixedResidueIdealContinued K I hI N χ) := by
  have hm := (mixedIdealResidueFlowTheta_unitAverage_entire K I hI N hcop χ hχ).comp
    (by fun_prop : Differentiable ℂ (fun s : ℂ => (Module.finrank ℚ K : ℂ)*s/2))
  have hp := differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos (integralIdealFractionalUnit I hI)).ne'))
  exact (((mixedInverseGammaFactor_entire K).const_mul _).mul hp).mul hm

theorem mixedResidueIdealContinued_eq_series
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ) [NeZero N]
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ) (hχ : χ ≠ 1)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (z:𝓞 K)) = 1)
    {s : ℂ} (hs : 1 < s.re) :
    mixedResidueIdealContinued K I hI N χ s =
      ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
        idealResidueCoefficient I hI N χ J *
          ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ)^(-s) := by
  have hg := mixedGammaFactor_ne_zero K (lt_trans zero_lt_one hs)
  have hc := mixedResidueIdealMellinFactor_ne_zero K
  have hi : ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos _).ne'
  have hp : ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val : ℝ) : ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hi)
  have HM := mixedIdealResidueFlowTheta_mellin K I hI N χ hχ hunit hs
  have HF : (torsionOrder K : ℂ)*((mixedRadialJacobian K : ℂ)*mixedGammaFactor K s) =
      mixedResidueIdealMellinFactor K * mixedGammaFactor K s := by
    unfold mixedResidueIdealMellinFactor
    ring
  rw [HF] at HM
  rw [mixedResidueIdealContinued, HM, mixedInverseGammaFactor, Complex.cpow_neg]
  field_simp

end
end ArtinMatthews.VaryingKummerAnalytic
