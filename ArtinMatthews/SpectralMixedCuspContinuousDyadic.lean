module

public import ArtinMatthews.SpectralKFrameContinuousIntegral
public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralEisensteinCoefficientLp
public import ArtinMatthews.SpectralPrimitiveFourierAmplitude
public import ArtinMatthews.SpectralMixedCuspPhysicalContinuous
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual continuous channel amplitudes at the source cusp 1/s
satisfy the same dyadic orbit bound as the principal cuspidal modes. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

def gamma0ContinuousFourierMass (N : ℕ) [NeZero N] (b : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (t : ℝ) : ℝ :=
  ∑ i : Gamma0EisensteinCuspClasses N,
    ‖gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N i)
      b Y hY n hn (eisensteinCriticalPoint t)‖^2

def gamma0ContinuousPrincipalDensity (N : ℕ) [NeZero N] (b : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (t : ℝ) : ℝ :=
  gamma0ContinuousFourierMass N b Y hY n hn t / Real.cosh (Real.pi*t)

theorem gamma0MixedCusp_continuous_dyadic_orbit_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ (n : ℤ) (hn : n ≠ 0) {T Y : ℝ}, 1/2 ≤ T → ∀ hY : 0 < Y,
      Y < (T/16)/(|cuspFourierFrequency 1 n|/
        (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) →
      let f := gamma0ContinuousPrincipalDensity (r*s) (gamma0CuspOneOver s) Y hY n hn
      IntegrableOn f (spectralPrincipalBand T) gamma0EisensteinSpectralMeasure ∧
        (∫ t in spectralPrincipalBand T, f t ∂gamma0EisensteinSpectralMeasure) ≤
          C*(T^2+|cuspFourierFrequency 1 n| * T/((r*s : ℕ) : ℝ)) := by
  obtain ⟨C,hC,hFrame⟩ := spectralKFrame_principal_integral_bound
  refine ⟨192*C,by positivity,?_⟩
  intro r s ir is hcop n hn T Y hT hY hYA
  let N := r*s
  let b := gamma0CuspOneOver s
  let q := |cuspFourierFrequency 1 n|
  let A := gamma0ContinuousFourierMass N b Y hY n hn
  let V := 6*(1+2*q/((N : ℝ)*(T/16)))
  let μ := gamma0EisensteinSpectralMeasure
  have hT₀ : 0 < T := by linarith
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hA (t : ℝ) : 0 ≤ A t := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hMom (F : ℝ → ℝ) (hF : spectralKFrameProfileBound T F) :
      Integrable (fun t => A t*‖spectralCompactRealKTransform F t‖^2) μ ∧
        (∫ t, A t*‖spectralCompactRealKTransform F t‖^2 ∂μ) ≤ V*spectralKFrameLength := by
    rcases hF with ⟨hs,hc,hS,hm⟩
    obtain ⟨hI,hM⟩ := gamma0MixedCusp_physical_continuous_moment r s hcop n hn F hs hc
      (by positivity : 0 < T/16) hY hYA hS
    simp only [norm_mul,mul_pow,← Finset.sum_mul] at hI hM
    exact ⟨hI,hM.trans (mul_le_mul_of_nonneg_left hm hV)⟩
  obtain ⟨hI,hB⟩ := hFrame μ A hA T V hT hV hMom
  refine ⟨hI,hB.trans ?_⟩
  change C*T^2*V ≤ (192*C)*(T^2+q*T/(N : ℝ))
  have hQ : 0 ≤ q*T/(N : ℝ) := by dsimp only [q]; positivity
  calc
    _ = (6*C)*(T^2+32*(q*T/(N : ℝ))) := by
      dsimp only [V]
      field_simp [hN.ne',hT₀.ne']
      ring
    _ ≤ (6*C)*(32*(T^2+q*T/(N : ℝ))) :=
      mul_le_mul_of_nonneg_left (by linarith only [sq_nonneg T]) (by positivity)
    _ = _ := by ring

end ArtinMatthews
