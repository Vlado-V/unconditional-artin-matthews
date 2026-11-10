module

public import ArtinMatthews.GiantComparisonArcMellin
public import ArtinMatthews.GiantComparisonMellinTail
public import ArtinMatthews.GiantComparisonMellinCore
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! At the actual comparison scales, the retained normalized Mellin energy
implies the local additive energy with the original factor of Y. -/
namespace ArtinMatthews
open Filter Finset MeasureTheory AddCircle
open scoped BigOperators
noncomputable section

theorem giantComparisonNatFourier_arc_log_bound (c C D A : ℝ)
    (hc : 0 < c) (hcC : c ≤ C) (hD : 0 ≤ D) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℕ) (a : ℕ → ℂ) (r Y H : ℝ),
      0 < Y → 1 ≤ H → H ≤ Y → (∀ w ∈ S, (w : ℝ) ∈ Set.Icc (c*Y) (C*Y)) →
      (∑ w ∈ S, ‖a w‖^2) ≤ Y*L^D →
      (∫ t in Set.Icc (-(L*(Y/H))) (L*(Y/H)),
        ‖(Y : ℂ)⁻¹ * giantComparisonMellinPolynomial S (giantComparisonArcTwist r a) t‖^2) ≤
          L^(-(A+2)) →
      (∫ t in Set.Icc (r-H⁻¹) (r+H⁻¹),
        ‖giantComparisonNatFourier S a (t : AddCircle (1 : ℝ))‖^2) ≤ Y*L^(-A) := by
  have hC : 0 ≤ C := hc.le.trans hcC
  obtain ⟨n, htail⟩ := giantComparisonMellinPolynomial_weighted_log_bound C D (A+1)
    hC hD (by linarith)
  obtain ⟨K, hK, harc⟩ := giantComparisonNatFourier_arc_energy_le c C hc hcC (n+2) (by omega)
  filter_upwards [htail, eventually_ge_atTop (max 1 K)] with L htail hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hKL : K ≤ L := (le_max_right _ _).trans hL
  intro S a r Y H hY hH hHY hS henergy hcore
  let a' := giantComparisonArcTwist r a
  let N := ⌊C*Y⌋₊
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hX : 0 < Y/H := div_pos hY hHpos
  have hXY : Y/H ≤ Y := div_le_self hY.le hH
  have hN : (N : ℝ) ≤ C*Y := Nat.floor_le (mul_nonneg hC hY.le)
  have hsub : S ⊆ Ioc 0 N := by
    intro w hw
    have h := hS w hw
    exact mem_Ioc.mpr ⟨Nat.cast_pos.mp ((mul_pos hc hY).trans_le h.1),
      (Nat.le_floor_iff (mul_nonneg hC hY.le)).mpr h.2⟩
  have hmass : (∑ w ∈ S, ‖a' w‖^2) ≤ Y*L^D := by
    simpa only [a', giantComparisonArcTwist_norm] using henergy
  have hcore' : (∫ t in Set.Icc (-(L*(Y/H))) (L*(Y/H)),
      ‖giantComparisonMellinPolynomial S a' t‖^2) ≤ Y^2*L^(-((A+1)+1)) := by
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY, mul_pow] at hcore
    rw [integral_const_mul, inv_pow, mul_comm ((Y^2)⁻¹), ← div_eq_mul_inv] at hcore
    have h := (div_le_iff₀ (sq_pos_of_pos hY)).mp hcore
    simpa only [a', mul_comm, show (A+1)+1 = A+2 by ring] using h
  have hbound := htail S N hsub a' (Y/H) Y hX hXY hN hmass hcore'
  have hden (t : ℝ) :
      sourceLocalMellinEnergyDensity S (fun w => (w : ℝ)) a' Y H (n+2) t =
        markedMajorFourierWeight (Y/H) (n+2) t * ‖giantComparisonMellinPolynomial S a' t‖^2 := by
    unfold sourceLocalMellinEnergyDensity sourceLocalMellinPolynomial markedMajorFourierWeight
      giantComparisonMellinPolynomial
    simp only [Complex.ofReal_natCast]
    rw [show |t|/(Y/H) = H*|t|/Y by field_simp]
  refine (harc S a r Y H hY hHpos hHY hS).trans ?_
  simp_rw [← show a' = giantComparisonArcTwist r a from rfl, hden]
  calc
    _ ≤ K*(Y⁻¹*(Y^2*L^(-(A+1)))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hY.le)) hK.le
    _ ≤ L*(Y⁻¹*(Y^2*L^(-(A+1)))) := mul_le_mul_of_nonneg_right hKL (by positivity)
    _ = _ := by
      rw [show -(A+1)=-A+(-1) by ring, Real.rpow_add hLp, Real.rpow_neg_one]
      field_simp

end
end ArtinMatthews
