module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Concrete real derivatives on the two-dimensional cusp coordinate plane. -/
noncomputable section
open Set Filter
open scoped ContDiff
namespace ArtinMatthews

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def spectralPlaneDerivative (a b : F) : (ℝ × ℝ) →L[ℝ] F :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight a + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight b

theorem spectralPlaneDerivative_apply (a b : F) (v : ℝ × ℝ) :
    spectralPlaneDerivative a b v = v.1 • a + v.2 • b := rfl

theorem spectralPlaneDerivative_norm_le (a b : F) :
    ‖spectralPlaneDerivative a b‖ ≤ ‖a‖+‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro p
  rw [spectralPlaneDerivative_apply]
  calc
    _ ≤ ‖p.1 • a‖ + ‖p.2 • b‖ := norm_add_le _ _
    _ = ‖p.1‖*‖a‖ + ‖p.2‖*‖b‖ := by rw [norm_smul,norm_smul]
    _ ≤ ‖p‖*‖a‖ + ‖p‖*‖b‖ := add_le_add
      (mul_le_mul_of_nonneg_right (norm_fst_le p) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (norm_snd_le p) (norm_nonneg _))
    _ = (‖a‖+‖b‖)*‖p‖ := by ring

def spectralPlaneDerivativeMap : (F × F) →L[ℝ] ((ℝ × ℝ) →L[ℝ] F) :=
  (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) F (ContinuousLinearMap.fst ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.fst ℝ F F) +
    (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) F (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.snd ℝ F F)

theorem spectralPlaneDerivativeMap_apply (a b : F) :
    spectralPlaneDerivativeMap (a,b) = spectralPlaneDerivative a b := rfl

theorem hasFDerivAt_spectralPlaneDerivative {a b : (ℝ × ℝ) → F}
    {a' b' : (ℝ × ℝ) →L[ℝ] F} {p : ℝ × ℝ}
    (ha : HasFDerivAt a a' p) (hb : HasFDerivAt b b' p) :
    HasFDerivAt (fun q => spectralPlaneDerivative (a q) (b q))
      (spectralPlaneDerivativeMap.comp (a'.prod b')) p := by
  exact (spectralPlaneDerivativeMap.hasFDerivAt).comp p (ha.prodMk hb)

theorem spectralPlaneDerivativeMap_derivative_norm_le
    (a' b' : (ℝ × ℝ) →L[ℝ] F) :
    ‖spectralPlaneDerivativeMap.comp (a'.prod b')‖ ≤ 2*(‖a'‖+‖b'‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  change ‖spectralPlaneDerivative (a' p) (b' p)‖ ≤ _
  calc
    _ ≤ ‖a' p‖+‖b' p‖ := spectralPlaneDerivative_norm_le _ _
    _ ≤ ‖a'‖*‖p‖+‖b'‖*‖p‖ := add_le_add (a'.le_opNorm p) (b'.le_opNorm p)
    _ ≤ (2*(‖a'‖+‖b'‖))*‖p‖ := by nlinarith [norm_nonneg a',norm_nonneg b',norm_nonneg p]

end ArtinMatthews
