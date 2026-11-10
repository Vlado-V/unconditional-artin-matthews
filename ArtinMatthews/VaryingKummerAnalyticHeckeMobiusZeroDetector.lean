module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusMellin
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusTruncationBound
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCriticalBound
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

/-! The actual Möbius zero detector after a proved quarter-line shift.
Every growth input is discharged by the genuine primitive functional
equation and ideal-series estimates. The target zero remains a hypothesis;
no zero-free region or detector saving is assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory
open OAI.SevenEighths.GammaZeroDetector
open scoped NumberField nonZeroDivisors Classical
noncomputable section

theorem exists_actual_mobius_zero_detector_bound
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧
      ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
        (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
        (_hnp : ψ.IsNonprincipal) (D Y : ℝ), 1 ≤ D → 1 ≤ Y →
        ∀ ρ : ℂ, (3/4 : ℝ) ≤ ρ.re → ψ.primitiveContinued hM hprim ρ=0 →
        ‖ψ.mobiusSmoothedSum D ρ Y‖ ≤ C*(Ideal.absNorm M : ℝ)^(3/8 : ℝ)*
          D^(1/2+ε)*(|ρ.im|+2)^m*Y^(-(1/4 : ℝ)) := by
  obtain ⟨CL,m,hCL,hL⟩ := exists_primitiveContinued_halfplane_polynomial_bound K
  obtain ⟨CM,hCM,hMbound⟩ := exists_mobiusTruncation_norm_bound K ε hε
  obtain ⟨G,hG,hdet⟩ := literal_detector_bound m
  let k : ℝ := ‖((2*Real.pi : ℝ) : ℂ)⁻¹‖ * Real.pi * G * CL * CM
  have hk : 0 ≤ k := by dsimp [k]; positivity
  refine ⟨k+1,m,by linarith,?_⟩
  intro M ψ hM hprim hnp D Y hD hY ρ hρ hz
  let f : ℂ → ℂ := fun z => ψ.primitiveContinued hM hprim (ρ+z)
  let g : ℂ → ℂ := fun z => ψ.mobiusTruncation D (ρ+z)
  let A : ℝ := CL*(Ideal.absNorm M : ℝ)^(3/8 : ℝ)*(|ρ.im|+2)^m
  let B : ℝ := CM*D^(1/2+ε)
  have hf : Differentiable ℂ f := (ψ.primitiveContinued_entire hM hprim).comp
    ((differentiable_const ρ).add differentiable_id)
  have hg : Differentiable ℂ g := (ψ.mobiusTruncation_entire D).comp
    ((differentiable_const ρ).add differentiable_id)
  have hf0 : f 0 = 0 := by simpa only [f,add_zero] using hz
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfb (z : ℂ) (hza : -(1/4 : ℝ) ≤ z.re) (_hzb : z.re ≤ 2) :
      ‖f z‖ ≤ A*(1+|z.im|)^m := by
    have hr : (1/2 : ℝ) ≤ (ρ+z).re := by simp only [add_re]; linarith
    have H := hL ψ hM hprim hnp (ρ+z) hr
    have him : |(ρ+z).im|+2 ≤ (|ρ.im|+2)*(1+|z.im|) := by
      simp only [add_im]
      nlinarith [abs_add_le ρ.im z.im,abs_nonneg ρ.im,abs_nonneg z.im,
        mul_nonneg (abs_nonneg ρ.im) (abs_nonneg z.im)]
    apply H.trans
    have Hpow := pow_le_pow_left₀ (by positivity : 0 ≤ |(ρ+z).im|+2) him m
    have hfac : 0 ≤ CL*(Ideal.absNorm M : ℝ)^(3/8 : ℝ) := by positivity
    have Hmul := mul_le_mul_of_nonneg_left Hpow hfac
    simpa only [A,mul_pow,mul_assoc] using Hmul
  have hgb (z : ℂ) (hza : -(1/4 : ℝ) ≤ z.re) (_hzb : z.re ≤ 2) : ‖g z‖ ≤ B := by
    exact hMbound ψ D hD (ρ+z) (by simp only [add_re]; linarith)
  have Hdet := hdet f g Y A B hf hg hf0 hY hA hB hfb hgb
  have heq : ψ.mobiusSmoothedSum D ρ Y = ((2*Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, literalKernel f g Y ((2 : ℂ)+(t : ℂ)*I) := by
    rw [ψ.mobiusSmoothedSum_mellin hM hprim hnp (zero_le_one.trans hD)
      (zero_lt_one.trans_le hY) (by linarith : -1 < ρ.re)]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      unfold literalKernel f g OAI.SevenEighths.GammaDetectorExpansion.line
      ring
  rw [heq,norm_mul]
  have H := mul_le_mul_of_nonneg_left Hdet (norm_nonneg (((2*Real.pi : ℝ) : ℂ)⁻¹))
  have H' : ‖((2*Real.pi : ℝ) : ℂ)⁻¹‖ *
      ‖∫ t : ℝ, literalKernel f g Y ((2 : ℂ)+(t : ℂ)*I)‖ ≤
      k*(Ideal.absNorm M : ℝ)^(3/8 : ℝ)*D^(1/2+ε)*(|ρ.im|+2)^m*Y^(-(1/4 : ℝ)) := by
    convert H using 1
    dsimp [k,A,B]
    ring
  apply H'.trans
  have hp : 0 ≤ (Ideal.absNorm M : ℝ)^(3/8 : ℝ)*D^(1/2+ε)*(|ρ.im|+2)^m*Y^(-(1/4 : ℝ)) := by
    positivity
  have HH := mul_le_mul_of_nonneg_right (show k ≤ k+1 by linarith) hp
  convert HH using 1 <;> ring

end
end ArtinMatthews.VaryingKummerAnalytic
