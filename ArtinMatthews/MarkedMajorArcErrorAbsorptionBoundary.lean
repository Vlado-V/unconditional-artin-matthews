module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ArtinMatthews.MarkedBonferroniTail
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform numerical absorption of the literal smoothing boundary term. -/

namespace ArtinMatthews

open Filter
open scoped Topology

lemma marked_major_smoothed_upper {L D η x : ℝ} (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hx : 0 ≤ x) (hxhi : x ≤ Real.exp (η*L)) :
    (1+L^(-D))*x ≤ Real.exp ((η+1)*L) := by
  have hε : L^(-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hfactor : 1+L^(-D) ≤ Real.exp L := by
    have hh := Real.add_one_le_exp L
    linarith
  calc
    _ ≤ Real.exp L * x := mul_le_mul_of_nonneg_right hfactor hx
    _ ≤ Real.exp L * Real.exp (η*L) := mul_le_mul_of_nonneg_left hxhi (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

noncomputable def markedMajorBoundaryEnvelope (η τ D L : ℝ) : ℝ :=
  3*(η+1)*L^(1-D) + 2*(η+1)*L*Real.exp (-τ*L)

lemma marked_major_boundary_le_envelope {η τ D L u v : ℝ}
    (hL : 1 ≤ L) (hD : 0 ≤ D) (hτ : 0 < τ) (hη : 0 < η)
    (hlo : Real.exp (τ*L) ≤ u) (huv : u ≤ v) (hv2 : v ≤ 2*u)
    (hhi : v ≤ Real.exp (η*L)) :
    (L^(-D)*(u+v)+2)*(Real.log ((1+L^(-D))*v)/u) ≤
      markedMajorBoundaryEnvelope η τ D L := by
  have hLp : 0 < L := by linarith
  have hu0 : 0 < u := (Real.exp_pos _).trans_le hlo
  have hv0 : 0 < v := hu0.trans_le huv
  have hε : 0 ≤ L^(-D) := Real.rpow_nonneg hLp.le _
  have hone : 1 ≤ Real.exp (τ*L) := by
    have hh := Real.add_one_le_exp (τ*L)
    nlinarith [mul_nonneg hτ.le hLp.le]
  have hvone : 1 ≤ v := hone.trans (hlo.trans huv)
  have harg : 0 < (1+L^(-D))*v := by positivity
  have hlog0 : 0 ≤ Real.log ((1+L^(-D))*v) :=
    Real.log_nonneg (by nlinarith [mul_nonneg hε hv0.le])
  have hlog : Real.log ((1+L^(-D))*v) ≤ (η+1)*L := by
    have hh := Real.log_le_log harg (marked_major_smoothed_upper hL hD hv0.le hhi)
    rwa [Real.log_exp] at hh
  have hinv : 1/u ≤ Real.exp (-τ*L) := by
    calc
      _ ≤ 1/Real.exp (τ*L) := div_le_div_of_nonneg_left zero_le_one (Real.exp_pos _) hlo
      _ = _ := by rw [show -τ*L = -(τ*L) by ring, Real.exp_neg, one_div]
  have hnum : L^(-D)*(u+v)+2 ≤ 3*L^(-D)*u+2 := by
    nlinarith [mul_le_mul_of_nonneg_left hv2 hε]
  have hpow : L^(-D)*L = L^(1-D) := by
    calc
      _ = L^(-D)*L^(1 : ℝ) := by rw [Real.rpow_one]
      _ = L^(-D+1) := (Real.rpow_add hLp _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ (3*L^(-D)*u+2)*(Real.log ((1+L^(-D))*v)/u) :=
      mul_le_mul_of_nonneg_right hnum (div_nonneg hlog0 hu0.le)
    _ = (3*L^(-D)+2/u)*Real.log ((1+L^(-D))*v) := by field_simp
    _ ≤ (3*L^(-D)+2/u)*((η+1)*L) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ (3*L^(-D)+2*Real.exp (-τ*L))*((η+1)*L) :=
      mul_le_mul_of_nonneg_right (by
        have hh : 2/u ≤ 2*Real.exp (-τ*L) := by
          simpa only [mul_one_div] using
            mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
        exact add_le_add (le_refl (3*L^(-D))) hh) (by positivity)
    _ = _ := by unfold markedMajorBoundaryEnvelope; rw [← hpow]; ring

theorem marked_major_boundary_envelope_tendsto (A η τ D : ℝ)
    (hτ : 0 < τ) (hD : A+1 < D) :
    Tendsto (fun L : ℝ => L^A * markedMajorBoundaryEnvelope η τ D L) atTop (𝓝 0) := by
  have h₁ := (tendsto_rpow_neg_atTop (show 0 < D-A-1 by linarith)).const_mul (3*(η+1))
  have h₂ := (rpow_mul_exp_neg_rpow_tendsto (A+1) (by norm_num : (0 : ℝ) < 1) hτ).const_mul
    (2*(η+1))
  simp only [Real.rpow_one, mul_zero] at h₂
  have hh := h₁.add h₂
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hp : L^A * L^(1-D) = L^(-(D-A-1)) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hlin : L^A * L = L^(A+1) := by rw [Real.rpow_add hL, Real.rpow_one]
  change 3*(η+1)*L^(-(D-A-1)) + 2*(η+1)*(L^(A+1)*Real.exp (-τ*L)) = _
  unfold markedMajorBoundaryEnvelope
  rw [← hp, ← hlin]
  ring

theorem marked_major_boundary_uniform_power (A η τ D c : ℝ)
    (hA : 0 ≤ A) (hτ : 0 < τ) (hη : 0 < η) (hD : A+3 < D) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ u v : ℝ,
      Real.exp (τ*L) ≤ u → u ≤ v → v ≤ 2*u → v ≤ Real.exp (η*L) →
      (L^(-D)*(u+v)+2)*(Real.log ((1+L^(-D))*v)/u) ≤ c*L^(-A) := by
  have hs := (marked_major_boundary_envelope_tendsto A η τ D hτ (by linarith)).eventually
    (Iio_mem_nhds hc)
  filter_upwards [hs, eventually_ge_atTop (1 : ℝ)] with L hs hL u v hlo huv hv2 hhi
  have hLp : 0 < L := by linarith
  have hpow : 0 < L^A := Real.rpow_pos_of_pos hLp A
  have he := marked_major_boundary_le_envelope hL (by linarith : 0 ≤ D) hτ hη hlo huv hv2 hhi
  have hid : L^A * L^(-A) = 1 := by rw [← Real.rpow_add hLp]; simp
  apply (mul_le_mul_iff_of_pos_left hpow).mp
  calc
    _ ≤ L^A * markedMajorBoundaryEnvelope η τ D L := mul_le_mul_of_nonneg_left he hpow.le
    _ ≤ c := hs.le
    _ = _ := by rw [mul_left_comm, hid, mul_one]

end ArtinMatthews
