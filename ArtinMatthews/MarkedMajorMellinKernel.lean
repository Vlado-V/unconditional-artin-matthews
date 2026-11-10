module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import OAI.NumberTheory.EgyptianFractions.RealPhaseEnvelope
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! The actual moving two-variable major-arc kernel. Its compact support is
uniform in X≥1 and in the modulation parameter; no transform is postulated. -/
namespace ArtinMatthews
open Set
open scoped ContDiff
noncomputable section

def markedMajorMellinArgument (X : ℝ) (p : ℝ × ℝ) : ℝ :=
  X*Real.exp p.2*(Real.exp (p.1/X)-1)

def markedMajorMellinKernelFun (ρ ρ' ψ : SchwartzMap ℝ ℂ) (X theta : ℝ) (p : ℝ × ℝ) : ℂ :=
  ρ (Real.exp (p.2+p.1/X))*ρ' (Real.exp p.2)*ψ (markedMajorMellinArgument X p)*
    OAI.Problem337.RealPhase.phase (theta*markedMajorMellinArgument X p)

theorem markedMajorMellinArgument_eq (X : ℝ) (p : ℝ × ℝ) :
    markedMajorMellinArgument X p = X*(Real.exp (p.2+p.1/X)-Real.exp p.2) := by
  rw [markedMajorMellinArgument, Real.exp_add]
  ring

lemma majorMellin_log_lipschitz {a u v : ℝ} (ha : 0 < a) (hu : a ≤ u) (hv : a ≤ v) :
    |Real.log u-Real.log v| ≤ (1/a)*|u-v| := by
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.log) (f' := fun t => t⁻¹) (s := Ici a) (C := 1/a)
    (fun t ht => (Real.hasDerivAt_log (ha.trans_le ht).ne').hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (ha.trans_le ht))]
      simpa only [one_div] using one_div_le_one_div_of_le ha ht)
    (convex_Ici a) hv hu
  simpa only [Real.norm_eq_abs] using H

def markedMajorMellinSupportBox (a b R : ℝ) : Set (ℝ × ℝ) :=
  Icc (-(R/a)) (R/a) ×ˢ Icc (Real.log a) (Real.log b)

theorem markedMajorMellinKernel_support (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R X : ℝ} (ha : 0 < a) (hX : 0 < X)
    (hρ : tsupport ρ ⊆ Icc a b) (hρ' : tsupport ρ' ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (theta : ℝ) :
    Function.support (markedMajorMellinKernelFun ρ ρ' ψ X theta) ⊆ markedMajorMellinSupportBox a b R := by
  intro p hp
  have hp' : markedMajorMellinKernelFun ρ ρ' ψ X theta p ≠ 0 := hp
  have h₁ : ρ (Real.exp (p.2+p.1/X)) ≠ 0 := by
    intro h
    apply hp'
    simp [markedMajorMellinKernelFun,h]
  have h₂ : ρ' (Real.exp p.2) ≠ 0 := by
    intro h
    apply hp'
    simp [markedMajorMellinKernelFun,h]
  have h₃ : ψ (markedMajorMellinArgument X p) ≠ 0 := by
    intro h
    apply hp'
    simp [markedMajorMellinKernelFun,h]
  have hu := hρ (subset_tsupport _ h₁)
  have hv := hρ' (subset_tsupport _ h₂)
  have hw := hψ (subset_tsupport _ h₃)
  have hz : p.2 ∈ Icc (Real.log a) (Real.log b) := by
    constructor
    · simpa only [Real.log_exp] using Real.log_le_log ha hv.1
    · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hv.2
  have hlog := majorMellin_log_lipschitz ha hu.1 hv.1
  simp only [Real.log_exp, add_sub_cancel_left] at hlog
  have hphase : |markedMajorMellinArgument X p| ≤ R := abs_le.mpr hw
  rw [markedMajorMellinArgument_eq,abs_mul,abs_of_pos hX] at hphase
  have hζ : |p.1| ≤ R/a := by
    rw [abs_div,abs_of_pos hX] at hlog
    have H := mul_le_mul_of_nonneg_left hlog hX.le
    rw [mul_div_cancel₀ _ hX.ne'] at H
    have H' := mul_le_mul_of_nonneg_left hphase (inv_nonneg.mpr ha.le)
    simp only [div_eq_mul_inv,one_mul] at H H' ⊢
    nlinarith
  exact ⟨abs_le.mp hζ,hz⟩

theorem markedMajorMellinKernel_tsupport (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R X : ℝ} (ha : 0 < a) (hX : 0 < X)
    (hρ : tsupport ρ ⊆ Icc a b) (hρ' : tsupport ρ' ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (theta : ℝ) :
    tsupport (markedMajorMellinKernelFun ρ ρ' ψ X theta) ⊆ markedMajorMellinSupportBox a b R :=
  closure_minimal (markedMajorMellinKernel_support ρ ρ' ψ ha hX hρ hρ' hψ theta)
    (isClosed_Icc.prod isClosed_Icc)

theorem markedMajorMellinKernel_contDiff (ρ ρ' ψ : SchwartzMap ℝ ℂ) (X theta : ℝ) :
    ContDiff ℝ ∞ (markedMajorMellinKernelFun ρ ρ' ψ X theta) := by
  unfold markedMajorMellinKernelFun markedMajorMellinArgument OAI.Problem337.RealPhase.phase
  have hcast : ContDiff ℝ ∞ (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  fun_prop

theorem markedMajorMellinKernel_hasCompactSupport (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R X : ℝ} (ha : 0 < a) (hX : 0 < X)
    (hρ : tsupport ρ ⊆ Icc a b) (hρ' : tsupport ρ' ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (theta : ℝ) :
    HasCompactSupport (markedMajorMellinKernelFun ρ ρ' ψ X theta) :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (isClosed_tsupport _)
    (markedMajorMellinKernel_tsupport ρ ρ' ψ ha hX hρ hρ' hψ theta)

def markedMajorMellinKernel (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R X : ℝ} (ha : 0 < a) (hX : 0 < X)
    (hρ : tsupport ρ ⊆ Icc a b) (hρ' : tsupport ρ' ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (theta : ℝ) : SchwartzMap (ℝ × ℝ) ℂ :=
  (markedMajorMellinKernel_hasCompactSupport ρ ρ' ψ ha hX hρ hρ' hψ theta).toSchwartzMap
    (markedMajorMellinKernel_contDiff ρ ρ' ψ X theta)

theorem markedMajorMellinKernel_coordinates (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {X w w' : ℝ} (hX : X ≠ 0) (hw : 0 < w) (hw' : 0 < w') (theta : ℝ) :
    markedMajorMellinKernelFun ρ ρ' ψ X theta (X*(Real.log w-Real.log w'),Real.log w') =
      ρ w*ρ' w'*ψ (X*(w-w'))*OAI.Problem337.RealPhase.phase (theta*(X*(w-w'))) := by
  have hwarg : Real.exp (Real.log w'+X*(Real.log w-Real.log w')/X) = w := by
    rw [mul_div_cancel_left₀ _ hX]
    have he : Real.log w'+(Real.log w-Real.log w') = Real.log w := by ring
    rw [he,Real.exp_log hw]
  have harg : markedMajorMellinArgument X (X*(Real.log w-Real.log w'),Real.log w') = X*(w-w') := by
    rw [markedMajorMellinArgument_eq]
    simp only [hwarg,Real.exp_log hw']
  simp only [markedMajorMellinKernelFun,hwarg,Real.exp_log hw',harg]

theorem markedMajorMellinKernel_on_source (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {X w w' : ℝ} (hX : X ≠ 0) (hw : 0 < w) (hw' : 0 < w')
    (hρ : ρ w = 1) (hρ' : ρ' w' = 1) (theta : ℝ) :
    markedMajorMellinKernelFun ρ ρ' ψ X theta (X*(Real.log w-Real.log w'),Real.log w') =
      ψ (X*(w-w'))*OAI.Problem337.RealPhase.phase (theta*(X*(w-w'))) := by
  rw [markedMajorMellinKernel_coordinates ρ ρ' ψ hX hw hw',hρ,hρ']
  simp only [one_mul]

end
end ArtinMatthews
