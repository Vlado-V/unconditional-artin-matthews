module

public import ArtinMatthews.SpectralFourierParabolicUnfolding
public import ArtinMatthews.SpectralCuspTranslationAdmissibility
public import ArtinMatthews.SpectralCuspTwoCellFourier
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralHorizontalPeriodMeasurable
public import ArtinMatthews.SpectralHyperbolicBochnerCoordinates
public import ArtinMatthews.SpectralWeylPlanarCoordinates
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact horizontal Fourier orthogonality for the existing compact
period-N window, with the invariant vertical density kept literal. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff MatrixGroups InnerProductSpace

namespace ArtinMatthews

theorem cuspFourierPhase_mul_star (w : ℝ) (m n : ℤ) (x : ℝ) :
    cuspFourierPhase w m x * star (cuspFourierPhase w n x) = cuspFourierPhase w (m-n) x := by
  rw [cuspFourierPhase_as_atkinPhase w m x,cuspFourierPhase_as_atkinPhase w n x,
    atkinPhase_conj,← atkinPhase_add,cuspFourierPhase_as_atkinPhase]
  congr 1
  push_cast
  ring

theorem cuspFourierPhase_integral_full_period (w : ℝ) (hw : 0 < w) (n : ℤ) :
    (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x) = if n = 0 then (w : ℂ) else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [cuspFourierPhase,cuspFourierFrequency]
  · rw [ite_eq_right hn]
    have h := cuspFourier_integral_deriv w hw n (fun _ => (1 : ℂ)) contDiff_const (fun _ => rfl)
    simp only [deriv_const,mul_zero,intervalIntegral.integral_zero,mul_one] at h
    exact (mul_eq_zero.mp h.symm).resolve_left
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr (cuspFourierFrequency_ne_zero w hw n hn)) Complex.I_ne_zero)

theorem cuspFourierWindow_phase_integral (w : ℝ) (hw : 0 < w) (n : ℤ) :
    (∫ x : ℝ, (spectralHorizontalPartition w x : ℂ)*cuspFourierPhase w n x) =
      if n = 0 then (w : ℂ) else 0 := by
  calc
    _ = ∫ x : ℝ, spectralHorizontalPartition w x • cuspFourierPhase w n x := by
      simp only [Complex.real_smul]
    _ = ∫ x in (0 : ℝ)..w, cuspFourierPhase w n x :=
      spectralHorizontalPartition_integral_of_locallyIntegrable hw
        (cuspFourierPhase_contDiff w n).continuous.locallyIntegrable
        (Eventually.of_forall (cuspFourierPhase_periodic w hw n))
    _ = _ := cuspFourierPhase_integral_full_period w hw n

def cuspFourierHeightPairing (ρ η : ℝ → ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), ρ y*η y/y^2

theorem cuspFourierTestSeed_inner_wave (N : ℕ) [NeZero N] (m n : ℤ) (ρ η : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    (∫ z : UpperHalfPlane, inner ℂ
      ((cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) m ρ hρ hcρ hpρ).val z)
      (cuspFourierWave N n η z)) =
      if m = n then (N : ℂ)*(cuspFourierHeightPairing ρ η : ℂ) else 0 := by
  let H (x : ℝ) := (spectralHorizontalPartition (N : ℝ) x : ℂ)*cuspFourierPhase (N : ℝ) (m-n) x
  let V (y : ℝ) := (ρ y*η y : ℝ)
  let D (y : ℝ) := V y/y^2
  have hpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hS : {p : ℝ × ℝ | 0 < p.2} = (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
    ext p
    simp
  have hi : (∫ x, H x) = if m = n then (N : ℂ) else 0 := by
    simpa only [H,sub_eq_zero,Complex.ofReal_natCast] using cuspFourierWindow_phase_integral (N : ℝ) hpos (m-n)
  calc
    _ = ∫ z : UpperHalfPlane, H z.re*(V z.im : ℂ) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [cuspFourierTestSeed_apply,cuspFourierWave,RCLike.inner_apply]
      have hreal : star ((spectralHorizontalPartition (N : ℝ) z.re*ρ z.im : ℝ) : ℂ) =
          ((spectralHorizontalPartition (N : ℝ) z.re*ρ z.im : ℝ) : ℂ) := by simp
      simp only [map_mul,starRingEnd_apply,star_star,hreal]
      unfold H V
      rw [← cuspFourierPhase_mul_star (N : ℝ) m n z.re]
      push_cast
      ring
    _ = ∫ p in {p : ℝ × ℝ | 0 < p.2}, H p.1*(D p.2 : ℂ) := by
      rw [upperHalfPlane_integral_coordinates_smul (fun p => H p.1*(V p.2 : ℂ))]
      apply setIntegral_congr_fun (by measurability)
      intro p _
      change (p.2^2)⁻¹ • (H p.1*(V p.2 : ℂ)) = H p.1*(D p.2 : ℂ)
      rw [Complex.real_smul,show (D p.2 : ℂ) = (V p.2 : ℂ)*(((p.2^2)⁻¹ : ℝ) : ℂ) by
        dsimp only [D]
        rw [div_eq_mul_inv,Complex.ofReal_mul]]
      ring
    _ = _ := by
      rw [hS,Measure.volume_eq_prod,setIntegral_prod_mul H (fun y : ℝ => (D y : ℂ)) univ (Ioi 0),
        setIntegral_univ,integral_complex_ofReal,hi]
      by_cases h : m = n
      · simp only [h,ite_true,cuspFourierHeightPairing,D,V]
      · simp only [h,ite_false,zero_mul]

end ArtinMatthews
