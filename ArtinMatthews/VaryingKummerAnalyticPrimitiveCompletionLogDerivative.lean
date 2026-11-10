module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletion
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAnalytic
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaVertical
public import ArtinMatthews.VaryingKummerAnalyticRayIdealLogDerivative
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

/-! Genuine logarithmic differentiation of the proper primitive completion,
with a degree-uniform vertical bound in its absolutely convergent region. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Set Filter
open scoped NumberField nonZeroDivisors Classical Topology
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) (hMt : M ≠ ⊤)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
include hprim

theorem properCompleted_logDeriv {s : ℂ} (hs : 1 < s.re) :
    logDeriv (ψ.properCompleted hM hMt) s =
      (Real.log (mixedConductorScale K (integralIdealFractionalUnit M hM)):ℂ) +
        logDeriv (mixedGammaFactor K) s + logDeriv ψ.dirichlet s := by
  have hA : (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).ne'
  have hP : (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hA)
  have hG := mixedGammaFactor_ne_zero K (zero_lt_one.trans hs)
  have hL := ψ.dirichlet_ne_zero hs
  have dP := differentiableAt_id.const_cpow (Or.inl hA) (x := s)
  have dG := mixedGammaFactor_differentiableAt K (zero_lt_one.trans hs)
  have dL := (ψ.dirichlet_analyticOnNhd s hs).differentiableAt
  have he : ψ.properCompleted hM hMt =ᶠ[𝓝 s]
      fun z => (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^z *
        mixedGammaFactor K z * ψ.dirichlet z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact ψ.properCompleted_eq_gamma_dirichlet hM hMt hprim hz
  rw [(logDeriv_congr_nhds he).eq_of_nhds]
  rw [logDeriv_fun_mul (f := fun z : ℂ =>
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^z * mixedGammaFactor K z)
      (g := ψ.dirichlet) s (mul_ne_zero hP hG) hL (dP.mul dG) dL,
    logDeriv_fun_mul (f := fun z : ℂ =>
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^z)
      (g := mixedGammaFactor K) s hP hG dP dG,
    Complex.logDeriv_const_cpow hA,
    ← Complex.ofReal_log (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).le]

end EvenIdealRayCharacter

universe u

theorem exists_properCompleted_logDeriv_vertical_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K]
      (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (hMt : M ≠ ⊤)
      (ψ : EvenIdealRayCharacter K M)
      (_hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
      (s : ℂ), 3/2 ≤ s.re → s.re ≤ 2 →
      ‖logDeriv (ψ.properCompleted hM hMt) s‖ ≤
        |Real.log (mixedConductorScale K (integralIdealFractionalUnit M hM))| +
          B*(Module.finrank ℚ K:ℝ)*Real.log (|s.im|+2) := by
  obtain ⟨B,hB,HB⟩ := exists_mixedGammaFactor_vertical_logarithmic_bound
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C := dedekindLogDerivUniformConstant / Real.log 2
  have hC : 0 < C := div_pos dedekindLogDerivUniformConstant_pos hlog2
  refine ⟨B+C,by positivity,?_⟩
  intro K _ _ M hM hMt ψ hprim s hs hs'
  have hL := ψ.dirichlet_logDeriv_norm_le hs
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
  rw [ψ.properCompleted_logDeriv hM hMt hprim (by linarith)]
  calc
    _ ≤ ‖(Real.log (mixedConductorScale K (integralIdealFractionalUnit M hM)):ℂ)‖ +
        ‖logDeriv (mixedGammaFactor K) s‖ + ‖logDeriv ψ.dirichlet s‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      rw [Complex.norm_real,Real.norm_eq_abs]
      nlinarith

end
end ArtinMatthews.VaryingKummerAnalytic
