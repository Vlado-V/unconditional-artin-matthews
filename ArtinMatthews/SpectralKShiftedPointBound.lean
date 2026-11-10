module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralBesselKEquation
public import ArtinMatthews.SpectralKShiftedDerivativeBound
public import ArtinMatthews.SpectralKShiftedMomentBound
public import ArtinMatthews.SpectralWeightedRayPointBound
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

/-! Pointwise polynomial decay in the physical variable, uniformly on
closed vertical order strips, with the normalized spectral exponential. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralKShiftedPoint_square_bound (k : ℕ) (B a : ℝ) (hB : 0 ≤ B)
    (hBk : B+1 < (k : ℝ)+1/2) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ t x : ℝ, |δ| ≤ B → a ≤ x →
      x^(2*k)*‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖^2 ≤
        C*(1+t^2)^k/Real.cosh (Real.pi*t) := by
  obtain ⟨M,hM,hMoment⟩ := spectralKShiftedMoment_uniform_bound k B hB (by linarith)
  obtain ⟨D,hD,hDeriv⟩ := spectralKShiftedDerivative_uniform_bound k B hB hBk
  have hk : 0 < k := by
    have hkR : 0 < (k : ℝ) := by linarith
    exact_mod_cast hkR
  let A : ℝ := (2*k : ℕ)/a+1
  have hA : 0 < A := by dsimp only [A];positivity
  refine ⟨A*M+D,by positivity,?_⟩
  intro δ t x hδ hx
  let f : ℝ → ℂ := schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I)
  have hi : IntegrableOn (fun y : ℝ => y^(2*k)*‖f y‖^2) (Ioi 0) :=
    spectralKShiftedMoment_integrable k δ t (by linarith)
  have hd : IntegrableOn (fun y : ℝ => y^(2*k)*‖deriv f y‖^2) (Ioi 0) :=
    spectralKShiftedDerivative_square_integrable k δ t (by linarith)
  have hsub : Ioi a ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi ha.le
  have hMomentTail : (∫ y in Ioi a,y^(2*k)*‖f y‖^2) ≤ spectralKShiftedMoment k δ t := by
    apply setIntegral_mono_set hi _ (Eventually.of_forall (fun _ hy => hsub hy))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg (pow_nonneg hy.le _) (sq_nonneg _)
  have hDerivTail : (∫ y in Ioi a,y^(2*k)*‖deriv f y‖^2) ≤
      ∫ y in Ioi (0 : ℝ),y^(2*k)*‖deriv f y‖^2 := by
    apply setIntegral_mono_set hd _ (Eventually.of_forall (fun _ hy => hsub hy))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg (pow_nonneg hy.le _) (sq_nonneg _)
  have hp := spectral_weighted_norm_sq_point_bound (2*k) (by omega) a ha f
    (fun y hy => (schlafliBesselK_hasDerivAt _ y (ha.trans_le hy)).differentiableAt)
    (hi.mono_set hsub) (hd.mono_set hsub) x hx
  calc
    _ ≤ A*(∫ y in Ioi a,y^(2*k)*‖f y‖^2)+∫ y in Ioi a,y^(2*k)*‖deriv f y‖^2 := hp
    _ ≤ A*spectralKShiftedMoment k δ t+
        ∫ y in Ioi (0 : ℝ),y^(2*k)*‖deriv f y‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hMomentTail hA.le) hDerivTail
    _ ≤ A*(M*(1+t^2)^k/Real.cosh (Real.pi*t))+D*(1+t^2)^k/Real.cosh (Real.pi*t) :=
      add_le_add (mul_le_mul_of_nonneg_left (hMoment δ t hδ) hA.le) (hDeriv δ t hδ)
    _ = _ := by ring

theorem spectral_exp_abs_le_two_cosh (u : ℝ) : Real.exp |u| ≤ 2*Real.cosh u := by
  rw [← Real.cosh_abs u,Real.cosh_eq]
  nlinarith [Real.exp_pos (-|u|)]

theorem schlafliBesselK_closed_strip_polynomial_bound (k : ℕ) (B a : ℝ) (hB : 0 ≤ B)
    (hBk : B+1 < (k : ℝ)+1/2) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ t x : ℝ, |δ| ≤ B → a ≤ x →
      Real.exp (Real.pi*|t|/2)*‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖ ≤
        C*(1+|t|)^k/x^k := by
  obtain ⟨C,hC,hbound⟩ := spectralKShiftedPoint_square_bound k B a hB hBk ha
  refine ⟨Real.sqrt (2*C),Real.sqrt_pos.mpr (by positivity),?_⟩
  intro δ t x hδ hx
  have hx0 : 0 < x := ha.trans_le hx
  have hcosh : 0 < Real.cosh (Real.pi*t) := Real.cosh_pos _
  have hp := (le_div_iff₀ hcosh).mp (hbound δ t x hδ hx)
  have he : Real.exp (Real.pi*|t|) ≤ 2*Real.cosh (Real.pi*t) := by
    simpa only [abs_mul,abs_of_pos Real.pi_pos] using spectral_exp_abs_le_two_cosh (Real.pi*t)
  have hmul := mul_le_mul_of_nonneg_left he
    (mul_nonneg (pow_nonneg hx0.le (2*k)) (sq_nonneg ‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖))
  have hnorm : x^(2*k)*‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖^2*
      Real.exp (Real.pi*|t|) ≤ 2*C*(1+t^2)^k := by nlinarith
  have ht : (1+t^2)^k ≤ ((1+|t|)^k)^2 := by
    have hh : 1+t^2 ≤ (1+|t|)^2 := by nlinarith [sq_abs t,abs_nonneg t]
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+t^2) hh k
    simpa only [← pow_mul,Nat.mul_comm 2 k] using hp
  have he2 : (Real.exp (Real.pi*|t|/2))^2 = Real.exp (Real.pi*|t|) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hxpow : (x^k)^2 = x^(2*k) := by rw [← pow_mul,Nat.mul_comm]
  have hsquare : (Real.exp (Real.pi*|t|/2)*x^k*‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖)^2 ≤
      2*C*((1+|t|)^k)^2 := by
    calc
      _ = x^(2*k)*‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖^2*Real.exp (Real.pi*|t|) := by
        rw [mul_pow,mul_pow,he2,hxpow]
        ring
      _ ≤ 2*C*(1+t^2)^k := hnorm
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (by positivity)
  have hsqrt : (Real.sqrt (2*C))^2 = 2*C := Real.sq_sqrt (by positivity)
  have hfinal : Real.exp (Real.pi*|t|/2)*x^k*‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖ ≤
      Real.sqrt (2*C)*(1+|t|)^k := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith [hsquare]
  apply (le_div_iff₀ (pow_pos hx0 k)).mpr
  calc
    _ = Real.exp (Real.pi*|t|/2)*x^k*‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖ := by ring
    _ ≤ _ := hfinal

theorem schlafliBesselK_three_quarter_strip_rapid_decay (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ t x : ℝ, |δ| ≤ 3/4 → 1 ≤ x →
      Real.exp (Real.pi*|t|/2)*‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖ ≤
        C*(1+|t|)^(N+2)/x^N := by
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  obtain ⟨C,hC,hbound⟩ := schlafliBesselK_closed_strip_polynomial_bound (N+2) (3/4) 1
    (by norm_num) (by push_cast;linarith) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro δ t x hδ hx
  apply (hbound δ t x hδ hx).trans
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hp : x^N ≤ x^(N+2) := pow_le_pow_right₀ hx (by omega)
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 N) hp

end ArtinMatthews
