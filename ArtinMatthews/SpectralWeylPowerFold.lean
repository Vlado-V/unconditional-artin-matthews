module

public import ArtinMatthews.SpectralWeylFoldSubstitution
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! Positive-power decay at zero controls the genuine folded Weyl
kernel when one height profile is no longer compactly supported. -/

noncomputable section
open Set
namespace ArtinMatthews

theorem spectralWeylFoldDensity_power_bound {X x u B M : ℝ}
    (hX : 0 < X) (hx : 0 < x) (hu : u ∈ Ioo (0 : ℝ) 1) (_hM : 0 ≤ M)
    (s t : ℝ) (f g : ℝ → ℂ) (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    ‖spectralWeylFoldDensity s t f g X (x,u)‖ ≤
      (4/X)*M*(X^2/(4*x))^B*(1-u^2)^(B-1)*‖g x‖ := by
  let w := 1-u^2
  let C := X^2/(4*x)
  let z := spectralWeylFoldHeight C u
  have hw : 0 < w := by
    dsimp [w]
    nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1+u by linarith [hu.1])]
  have hC : 0 < C := by dsimp [C]; positivity
  have hz : z = C*w := rfl
  have hz₀ : 0 < z := hz ▸ mul_pos hC hw
  have hcoef : ‖((4/(X*w)*Real.cos ((s*x+t*z)*u/Real.sqrt w) : ℝ) : ℂ)‖ ≤ 4/(X*w) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (by positivity : 0 < 4/(X*w))]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  change ‖((4/(X*w)*Real.cos ((s*x+t*z)*u/Real.sqrt w) : ℝ) : ℂ)*f z*star (g x)‖ ≤ _
  rw [norm_mul,norm_mul,norm_star]
  calc
    _ ≤ (4/(X*w))*(M*z^B)*‖g x‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul hcoef (hf z hz₀) (norm_nonneg _) (by positivity)) (norm_nonneg _)
    _ = _ := by
      rw [hz,Real.mul_rpow hC.le hw.le,Real.rpow_sub_one hw.ne']
      change (4/(X*w))*(M*(C^B*w^B))*‖g x‖ = (4/X)*M*C^B*(w^B/w)*‖g x‖
      field_simp [hX.ne',hw.ne']

theorem spectralWeylFoldDensity_compact_power_bound {X b u B M : ℝ}
    (hX : 0 < X) (hb : 0 < b) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (s t x : ℝ) (hx : 0 < x) (f g : ℝ → ℂ)
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B)
    (hg : ∀ x ∈ tsupport g, b ≤ x) :
    ‖spectralWeylFoldDensity s t f g X (x,u)‖ ≤
      ((4/X)*M*(X^2/(4*b))^B)*((1-u)^(B-1))*‖g x‖ := by
  by_cases hgx : g x = 0
  · simp only [spectralWeylFoldDensity,hgx,star_zero,mul_zero,norm_zero,le_refl]
  have hbx : b ≤ x := hg x (subset_tsupport g hgx)
  have hq : (X^2/(4*x))^B ≤ (X^2/(4*b))^B := by
    apply Real.rpow_le_rpow (by positivity) _ hB.le
    exact div_le_div_of_nonneg_left (sq_nonneg X) (by positivity) (by linarith)
  have hw : 0 < 1-u^2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1+u by linarith [hu.1])]
  have hv : 0 < 1-u := sub_pos.mpr hu.2
  have hvw : 1-u ≤ 1-u^2 := by nlinarith [hu.1,hu.2]
  have hp : (1-u^2)^(B-1) ≤ (1-u)^(B-1) :=
    Real.rpow_le_rpow_of_nonpos hv hvw (sub_nonpos.mpr hB₁)
  refine (spectralWeylFoldDensity_power_bound hX hx hu hM s t f g hf).trans ?_
  have hprod := mul_le_mul hq hp (Real.rpow_nonneg hw.le _) (Real.rpow_nonneg (by positivity) _)
  calc
    _ = ((4/X)*M)*((X^2/(4*x))^B*(1-u^2)^(B-1))*‖g x‖ := by ring
    _ ≤ ((4/X)*M)*((X^2/(4*b))^B*(1-u)^(B-1))*‖g x‖ := by gcongr
    _ = _ := by ring

end ArtinMatthews
