module

public import ArtinMatthews.SpectralKShiftedMoment
public import ArtinMatthews.SpectralKDerivativeAdjacentOrder
public import ArtinMatthews.SpectralKShiftedMomentBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Square-integrable shifted-order derivatives from the genuine
adjacent-order recurrence and the checked Mellin moments. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem schlafliBesselK_deriv_norm_sq_le (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖deriv (schlafliBesselK ν) x‖^2 ≤
      ‖schlafliBesselK (ν-1) x‖^2+‖schlafliBesselK (ν+1) x‖^2 := by
  have h : ‖deriv (schlafliBesselK ν) x‖ ≤
      (‖schlafliBesselK (ν-1) x‖+‖schlafliBesselK (ν+1) x‖)/2 := by
    rw [schlafliBesselK_deriv_adjacent_order ν hx,norm_mul]
    calc
      _ ≤ ‖(-(1/2) : ℂ)‖*(‖schlafliBesselK (ν-1) x‖+‖schlafliBesselK (ν+1) x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ = _ := by norm_num;ring
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖schlafliBesselK (ν-1) x‖-‖schlafliBesselK (ν+1) x‖)]

theorem spectralKShiftedDerivative_square_integrable (k : ℕ) (δ t : ℝ)
    (hδ : |δ|+1 < (k : ℝ)+1/2) :
    IntegrableOn (fun x : ℝ => x^(2*k)*‖deriv (schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I)) x‖^2) (Ioi 0) := by
  have hm : |δ-1| < (k : ℝ)+1/2 := by
    have h := abs_sub δ (1 : ℝ)
    norm_num at h
    linarith
  have hp : |δ+1| < (k : ℝ)+1/2 := by
    have h := abs_add_le δ (1 : ℝ)
    norm_num at h
    linarith
  have hi := (spectralKShiftedMoment_integrable k (δ-1) t hm).add
    (spectralKShiftedMoment_integrable k (δ+1) t hp)
  have hmeas : Measurable (fun x : ℝ => x^(2*k)*‖deriv (schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I)) x‖^2) := by
    have hd := measurable_deriv (schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I))
    fun_prop
  apply hi.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change 0 < x at hx
  dsimp only [Pi.add_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hx.le _) (sq_nonneg _))]
  have h := mul_le_mul_of_nonneg_left
    (schlafliBesselK_deriv_norm_sq_le ((δ : ℂ)+(t : ℂ)*Complex.I) hx) (pow_nonneg hx.le (2*k))
  have hem : ((δ : ℂ)+(t : ℂ)*Complex.I)-1 = ((δ-1 : ℝ) : ℂ)+(t : ℂ)*Complex.I := by push_cast;ring
  have hep : ((δ : ℂ)+(t : ℂ)*Complex.I)+1 = ((δ+1 : ℝ) : ℂ)+(t : ℂ)*Complex.I := by push_cast;ring
  simpa only [hem,hep,mul_add] using h

theorem spectralKShiftedDerivative_square_moment_bound (k : ℕ) (δ t : ℝ)
    (hδ : |δ|+1 < (k : ℝ)+1/2) :
    (∫ x in Ioi (0 : ℝ),x^(2*k)*‖deriv (schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I)) x‖^2) ≤
      spectralKShiftedMoment k (δ-1) t+spectralKShiftedMoment k (δ+1) t := by
  have hm : |δ-1| < (k : ℝ)+1/2 := by
    have h := abs_sub δ (1 : ℝ)
    norm_num at h
    linarith
  have hp : |δ+1| < (k : ℝ)+1/2 := by
    have h := abs_add_le δ (1 : ℝ)
    norm_num at h
    linarith
  unfold spectralKShiftedMoment
  rw [← integral_add (spectralKShiftedMoment_integrable k (δ-1) t hm)
    (spectralKShiftedMoment_integrable k (δ+1) t hp)]
  apply setIntegral_mono_on (spectralKShiftedDerivative_square_integrable k δ t hδ)
    ((spectralKShiftedMoment_integrable k (δ-1) t hm).add
      (spectralKShiftedMoment_integrable k (δ+1) t hp)) measurableSet_Ioi
  intro x hx
  change 0 < x at hx
  dsimp only [Pi.add_apply]
  have h := mul_le_mul_of_nonneg_left
    (schlafliBesselK_deriv_norm_sq_le ((δ : ℂ)+(t : ℂ)*Complex.I) hx) (pow_nonneg hx.le (2*k))
  have hem : ((δ : ℂ)+(t : ℂ)*Complex.I)-1 = ((δ-1 : ℝ) : ℂ)+(t : ℂ)*Complex.I := by push_cast;ring
  have hep : ((δ : ℂ)+(t : ℂ)*Complex.I)+1 = ((δ+1 : ℝ) : ℂ)+(t : ℂ)*Complex.I := by push_cast;ring
  simpa only [hem,hep,mul_add] using h

theorem spectralKShiftedDerivative_uniform_bound (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hBk : B+1 < (k : ℝ)+1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ t : ℝ, |δ| ≤ B →
      (∫ x in Ioi (0 : ℝ),x^(2*k)*‖deriv (schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I)) x‖^2) ≤
        C*(1+t^2)^k/Real.cosh (Real.pi*t) := by
  obtain ⟨C,hC,hbound⟩ := spectralKShiftedMoment_uniform_bound k (B+1) (by linarith) hBk
  refine ⟨2*C,by positivity,?_⟩
  intro δ t hδ
  have hm : |δ-1| ≤ B+1 := by
    have h := abs_sub δ (1 : ℝ)
    norm_num at h
    linarith
  have hp : |δ+1| ≤ B+1 := by
    have h := abs_add_le δ (1 : ℝ)
    norm_num at h
    linarith
  calc
    _ ≤ spectralKShiftedMoment k (δ-1) t+spectralKShiftedMoment k (δ+1) t :=
      spectralKShiftedDerivative_square_moment_bound k δ t (by linarith)
    _ ≤ C*(1+t^2)^k/Real.cosh (Real.pi*t)+C*(1+t^2)^k/Real.cosh (Real.pi*t) :=
      add_le_add (hbound (δ-1) t hm) (hbound (δ+1) t hp)
    _ = _ := by ring

end ArtinMatthews
