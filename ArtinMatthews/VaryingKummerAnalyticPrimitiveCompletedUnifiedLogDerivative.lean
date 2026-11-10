module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletedUnified
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAnalytic
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaVertical
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveConductorHeight
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveLogDerivative
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

/-! Actual logarithmic differentiation and uniform vertical bounds for
the unified primitive completion. The fixed conductor-one normalization has
already been removed in the genuine positive-half-plane identity. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Set Filter
open scoped NumberField nonZeroDivisors Classical Topology
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hnp : ψ.IsNonprincipal)
include hprim hnp

theorem primitiveCompletedUnified_logDeriv {s : ℂ} (hs : 1 < s.re) :
    logDeriv (ψ.primitiveCompletedUnified hM) s =
      (Real.log (mixedConductorScale K (integralIdealFractionalUnit M hM)):ℂ) +
        logDeriv (mixedGammaFactor K) s + logDeriv (ψ.primitiveContinued hM hprim) s := by
  have hA : (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).ne'
  have hP : (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hA)
  have hG := mixedGammaFactor_ne_zero K (zero_lt_one.trans hs)
  have hL := ψ.primitiveContinued_ne_zero_right hM hprim hnp hs
  have dP := differentiableAt_id.const_cpow (Or.inl hA) (x := s)
  have dG := mixedGammaFactor_differentiableAt K (zero_lt_one.trans hs)
  have dL := ψ.primitiveContinued_entire hM hprim s
  have he : ψ.primitiveCompletedUnified hM =ᶠ[𝓝 s]
      fun z => (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^z *
        mixedGammaFactor K z * ψ.primitiveContinued hM hprim z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact ψ.primitiveCompletedUnified_eq_gamma_primitive hM hprim hnp (zero_lt_one.trans hz)
  rw [(logDeriv_congr_nhds he).eq_of_nhds]
  rw [logDeriv_fun_mul (f := fun z : ℂ =>
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^z * mixedGammaFactor K z)
      (g := ψ.primitiveContinued hM hprim) s (mul_ne_zero hP hG) hL (dP.mul dG) dL,
    logDeriv_fun_mul (f := fun z : ℂ =>
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^z)
      (g := mixedGammaFactor K) s hP hG dP dG,
    Complex.logDeriv_const_cpow hA,
    ← Complex.ofReal_log (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).le]

theorem primitiveCompletedUnified_logDeriv_eq_dirichlet {s : ℂ} (hs : 1 < s.re) :
    logDeriv (ψ.primitiveCompletedUnified hM) s =
      (Real.log (mixedConductorScale K (integralIdealFractionalUnit M hM)):ℂ) +
        logDeriv (mixedGammaFactor K) s + logDeriv ψ.dirichlet s := by
  rw [ψ.primitiveCompletedUnified_logDeriv hM hprim hnp hs,
    ψ.primitiveContinued_logDeriv_eq_dirichlet hM hprim hnp hs]

end EvenIdealRayCharacter

universe u

theorem exists_primitiveCompletedUnified_logDeriv_vertical_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K]
      (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (ψ : EvenIdealRayCharacter K M)
      (_hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
      (_hnp : ψ.IsNonprincipal) (s : ℂ), 3/2 ≤ s.re → s.re ≤ 2 →
      ‖logDeriv (ψ.primitiveCompletedUnified hM) s‖ ≤
        |Real.log (mixedConductorScale K (integralIdealFractionalUnit M hM))| +
          B*(Module.finrank ℚ K:ℝ)*Real.log (|s.im|+2) := by
  obtain ⟨B,hB,HB⟩ := exists_mixedGammaFactor_vertical_logarithmic_bound
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C := dedekindLogDerivUniformConstant / Real.log 2
  have hC : 0 < C := div_pos dedekindLogDerivUniformConstant_pos hlog2
  refine ⟨B+C,by positivity,?_⟩
  intro K _ _ M hM ψ hprim hnp s hs hs'
  have hL := ψ.primitiveContinued_logDeriv_norm_le hM hprim hnp hs
  have hG := HB K s (by linarith) hs'
  have hl : Real.log 2 ≤ Real.log (|s.im|+2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hCL : dedekindLogDerivUniformConstant*(Module.finrank ℚ K:ℝ) ≤
      C*(Module.finrank ℚ K:ℝ)*Real.log (|s.im|+2) := by
    have hh := mul_le_mul_of_nonneg_left hl
      (mul_nonneg hC.le (Nat.cast_nonneg (Module.finrank ℚ K)))
    have he : C*(Module.finrank ℚ K:ℝ)*Real.log 2 =
        dedekindLogDerivUniformConstant*(Module.finrank ℚ K:ℝ) := by
      dsimp [C]
      field_simp
    rwa [he] at hh
  rw [ψ.primitiveCompletedUnified_logDeriv hM hprim hnp (by linarith)]
  calc
    _ ≤ ‖(Real.log (mixedConductorScale K (integralIdealFractionalUnit M hM)):ℂ)‖ +
        ‖logDeriv (mixedGammaFactor K) s‖ + ‖logDeriv (ψ.primitiveContinued hM hprim) s‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      rw [Complex.norm_real,Real.norm_eq_abs]
      nlinarith

theorem exists_primitiveCompletedUnified_logDeriv_conductor_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K]
      (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (ψ : EvenIdealRayCharacter K M)
      (_hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
      (_hnp : ψ.IsNonprincipal) (s : ℂ), 3/2 ≤ s.re → s.re ≤ 2 →
      ‖logDeriv (ψ.primitiveCompletedUnified hM) s‖ ≤
        Real.log |(discr K:ℝ)|/2 + Real.log (Ideal.absNorm M:ℝ)/2 +
          B*(Module.finrank ℚ K:ℝ)*Real.log (|s.im|+2) := by
  obtain ⟨B,hB,HB⟩ := exists_primitiveCompletedUnified_logDeriv_vertical_bound
  refine ⟨B+1,by positivity,?_⟩
  intro K _ _ M hM ψ hprim hnp s hs hs'
  have H := HB K M hM ψ hprim hnp s hs hs'
  have hscale := mixedConductorScale_integral_log_abs_le K M hM
  have hl : Real.log 2 ≤ Real.log (|s.im|+2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hnl := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (Module.finrank ℚ K):
    (0:ℝ) ≤ Module.finrank ℚ K)
  nlinarith

end
end ArtinMatthews.VaryingKummerAnalytic
