module

public import ArtinMatthews.SpectralKFrameContinuousIntegral
public import ArtinMatthews.SpectralInfinityContinuousPacket
public import ArtinMatthews.SpectralFiniteDyadicIntegral
public import ArtinMatthews.SpectralInfinityContinuousMoment
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

/-! The true infinity Fourier packet has a level-uniform continuous
spectral cutoff bound in its actual channel measure. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ArtinMatthews

def gamma0InfinityContinuousPacketDensity {ι : Type*} (N : ℕ) [NeZero N]
    (u : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (hn : ∀ j, n j ≠ 0)
    (Y : ℝ) (hY : 0 < Y) (t : ℝ) : ℝ :=
  (∑ i : Gamma0EisensteinCuspClasses N, ‖gamma0InfinityContinuousPacketFourier N u α n hn Y hY i t‖^2)/
    Real.cosh (Real.pi*t)

theorem gamma0Infinity_continuous_packet_dyadic_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (N : ℕ) [NeZero N]
      (u : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (hn : Function.Injective n) (hn₀ : ∀ j, n j ≠ 0)
      {T B Y : ℝ}, 1/2 ≤ T → 0 < B → ∀ hY : 0 < Y,
      Y < (T/16)/B → (∀ j, |cuspFourierFrequency 1 (n j)| ≤ B) →
      let f := gamma0InfinityContinuousPacketDensity N u α n hn₀ Y hY
      IntegrableOn f (spectralPrincipalBand T) gamma0EisensteinSpectralMeasure ∧
        (∫ t in spectralPrincipalBand T, f t ∂gamma0EisensteinSpectralMeasure) ≤
          C*(T^2+B*T/(N : ℝ))*(∑ j ∈ u, ‖α j‖^2) := by
  obtain ⟨C,hC,hFrame⟩ := spectralKFrame_principal_integral_bound
  refine ⟨192*C,by positivity,?_⟩
  intro ι N inst u α n hn hn₀ T B Y hT hB hY hYA hfreq
  let S := ∑ j ∈ u, ‖α j‖^2
  let W := gamma0InfinityContinuousPacketFourier N u α n hn₀ Y hY
  let A (t : ℝ) := ∑ i : Gamma0EisensteinCuspClasses N, ‖W i t‖^2
  let U := 6*(1+2*B/((N : ℝ)*(T/16)))
  let μ := gamma0EisensteinSpectralMeasure
  have hT₀ : 0 < T := by linarith
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hA (t : ℝ) : 0 ≤ A t := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hMom (F : ℝ → ℝ) (hF : spectralKFrameProfileBound T F) :
      Integrable (fun t => A t*‖spectralCompactRealKTransform F t‖^2) μ ∧
        (∫ t, A t*‖spectralCompactRealKTransform F t‖^2 ∂μ) ≤ U*S*spectralKFrameLength := by
    rcases hF with ⟨hs,hc,hSupp,hm⟩
    obtain ⟨hI,hM⟩ := gamma0Infinity_physical_continuous_moment N u α n hn hn₀ F hs hc
      (by positivity : 0 < T/16) hB hY hYA hSupp hfreq
    simp only [norm_mul,mul_pow,← Finset.mul_sum] at hI hM
    have heq : (fun t => A t*‖spectralCompactRealKTransform F t‖^2) =
        fun t => ‖spectralCompactRealKTransform F t‖^2*A t :=
      funext fun _ => mul_comm _ _
    rw [heq]
    refine ⟨hI,hM.trans ?_⟩
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hS) hU).trans_eq (by ring)
  obtain ⟨hI,hW⟩ := hFrame μ A hA T (U*S) hT (mul_nonneg hU hS) hMom
  refine ⟨hI,hW.trans ?_⟩
  change C*T^2*(U*S) ≤ (192*C)*(T^2+B*T/(N : ℝ))*S
  have hC₀ : C*T^2*U ≤ (192*C)*(T^2+B*T/(N : ℝ)) := by
    calc
      _ = (6*C)*(T^2+32*(B*T/(N : ℝ))) := by
        dsimp only [U]
        field_simp [hN.ne',hT₀.ne']
        ring
      _ ≤ (6*C)*(32*(T^2+B*T/(N : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith only [sq_nonneg T]) (by positivity)
      _ = _ := by ring
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right hC₀ hS

theorem gamma0Infinity_continuous_packet_cutoff_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (N : ℕ) [NeZero N]
      (u : Finset ι) (α : ι → ℂ) (n : ι → ℤ) (hn : Function.Injective n) (hn₀ : ∀ j, n j ≠ 0)
      {R B Y : ℝ}, 1 ≤ R → 0 < B → ∀ hY : 0 < Y,
      Y < (1/16)/B → (∀ j, |cuspFourierFrequency 1 (n j)| ≤ B) →
      let f := gamma0InfinityContinuousPacketDensity N u α n hn₀ Y hY
      let W := (fun t : ℝ => 1+|t|) ⁻¹' Icc 1 R
      IntegrableOn f W gamma0EisensteinSpectralMeasure ∧
        (∫ t in W, f t ∂gamma0EisensteinSpectralMeasure) ≤
          C*(R^2+B*R/(N : ℝ))*(∑ j ∈ u, ‖α j‖^2) := by
  obtain ⟨C,hC,hDyad⟩ := gamma0Infinity_continuous_packet_dyadic_bound
  refine ⟨2*C,by positivity,?_⟩
  intro ι N inst u α n hn hn₀ R B Y hR hB hY hYA hfreq
  let μ := gamma0EisensteinSpectralMeasure
  let f := gamma0InfinityContinuousPacketDensity N u α n hn₀ Y hY
  let τ (t : ℝ) := 1+|t|
  let S := ∑ j ∈ u, ‖α j‖^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hτ : Measurable τ := by unfold τ; fun_prop
  have hf (t : ℝ) : 0 ≤ f t := div_nonneg
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Real.cosh_pos _).le
  have hWin (k : ℕ) :
      IntegrableOn f (τ ⁻¹' Icc ((2 : ℝ)^k) (2*(2 : ℝ)^k)) μ ∧
        (∫ t in τ ⁻¹' Icc ((2 : ℝ)^k) (2*(2 : ℝ)^k), f t ∂μ) ≤
          (C*S)*(((2 : ℝ)^k)^2+(B/(N : ℝ))*(2 : ℝ)^k) := by
    let T : ℝ := 2^k
    have hT : 1 ≤ T := one_le_pow₀ (by norm_num)
    have hY' : Y < (T/16)/B := hYA.trans_le
      (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hT (by norm_num)) hB.le)
    have h := hDyad N u α n hn hn₀ (T := T) (B := B) (Y := Y)
      (by linarith only [hT]) hB hY hY' hfreq
    exact ⟨h.1,h.2.trans_eq (by ring)⟩
  obtain ⟨hI,hW⟩ := spectral_nonneg_dyadic_cutoff_integral_le μ τ f hτ hf hR
    (B := B/(N : ℝ)) (by positivity) (mul_nonneg hC.le hS) hWin
  exact ⟨hI,hW.trans_eq (by ring)⟩

end ArtinMatthews
