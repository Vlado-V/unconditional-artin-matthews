module

public import ArtinMatthews.MarkedMajorMellinKernel
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity
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

/-! Smooth extension of the actual major kernel in the compact parameter u=1/X. -/
namespace ArtinMatthews
open Set
open scoped ContDiff
noncomputable section

def majorMellinExprel (t : ℝ) : ℝ := (dslope Complex.exp 0 (t : ℂ)).re

theorem majorMellinExprel_contDiff : ContDiff ℝ ∞ majorMellinExprel := by
  have hd : Differentiable ℂ (dslope Complex.exp 0) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (by simp)).mpr
      Complex.differentiable_exp.differentiableOn)
  have hc : ContDiff ℝ ∞ (dslope Complex.exp 0) := hd.contDiff.restrict_scalars ℝ
  exact Complex.reCLM.contDiff.comp (hc.comp Complex.ofRealCLM.contDiff)

theorem majorMellinExprel_zero : majorMellinExprel 0 = 1 := by
  simp [majorMellinExprel,Complex.deriv_exp]

theorem majorMellinExprel_eq {t : ℝ} (ht : t ≠ 0) :
    majorMellinExprel t = (Real.exp t-1)/t := by
  rw [majorMellinExprel,dslope_of_ne _ (by exact_mod_cast ht)]
  simp only [slope, sub_zero, Complex.exp_zero, smul_eq_mul, ← Complex.ofReal_exp, vsub_eq_sub]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

def markedMajorMellinFamilyArgument (p : ℝ × (ℝ × ℝ)) : ℝ :=
  Real.exp p.2.2 * p.2.1 * majorMellinExprel (p.1*p.2.1)

theorem markedMajorMellinFamilyArgument_contDiff :
    ContDiff ℝ ∞ markedMajorMellinFamilyArgument := by
  unfold markedMajorMellinFamilyArgument
  have := majorMellinExprel_contDiff
  fun_prop

theorem markedMajorMellinFamilyArgument_eq {X : ℝ} (hX : X ≠ 0) (p : ℝ × ℝ) :
    markedMajorMellinFamilyArgument (X⁻¹,p) = markedMajorMellinArgument X p := by
  by_cases hz : p.1 = 0
  · simp [markedMajorMellinFamilyArgument,markedMajorMellinArgument,hz]
  · rw [markedMajorMellinFamilyArgument,majorMellinExprel_eq (mul_ne_zero (inv_ne_zero hX) hz)]
    unfold markedMajorMellinArgument
    dsimp
    rw [show X⁻¹*p.1=p.1/X by ring]
    field_simp


def markedMajorMellinFamilyAmplitude (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    (p : ℝ × (ℝ × ℝ)) : ℂ :=
  ρ (Real.exp (p.2.2+p.1*p.2.1))*ρ' (Real.exp p.2.2)*ψ (markedMajorMellinFamilyArgument p)

theorem markedMajorMellinFamilyAmplitude_contDiff (ρ ρ' ψ : SchwartzMap ℝ ℂ) :
    ContDiff ℝ ∞ (markedMajorMellinFamilyAmplitude ρ ρ' ψ) := by
  unfold markedMajorMellinFamilyAmplitude
  have := markedMajorMellinFamilyArgument_contDiff
  fun_prop

theorem markedMajorMellinKernel_family (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {X : ℝ} (hX : X ≠ 0) (theta : ℝ) (p : ℝ × ℝ) :
    markedMajorMellinKernelFun ρ ρ' ψ X theta p =
      markedMajorMellinFamilyAmplitude ρ ρ' ψ (X⁻¹,p) *
      OAI.Problem337.RealPhase.phase (theta*markedMajorMellinFamilyArgument (X⁻¹,p)) := by
  rw [markedMajorMellinFamilyAmplitude,markedMajorMellinFamilyArgument_eq hX]
  unfold markedMajorMellinKernelFun
  dsimp
  rw [show X⁻¹*p.1=p.1/X by ring]

end
end ArtinMatthews
