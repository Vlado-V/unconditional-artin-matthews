module

public import ArtinMatthews.HeckeDirichletTwist
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Uniform conductor and frequency budgets for the actual fixed-Hecke
long-prime estimate. -/

noncomputable section
namespace ArtinMatthews
open Filter OAI.SevenEighths
open scoped Topology

theorem heckeDirichletTwist_modulus_eventually (η : HeckeFamily.Character)
    (A δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A →
      ∀ χ : DirichletCharacter ℂ q,
        ((heckeDirichletTwist η χ).modulus.absNorm : ℝ) ≤ x^δ := by
  have hlim := ((isLittleO_log_rpow_rpow_atTop (2*A) hδ).tendsto_div_nhds_zero).const_mul
    (η.modulus.absNorm : ℝ)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro q _ hq χ
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hq2 : (q : ℝ)^2 ≤ (Real.log x)^(2*A) := by
    calc
      _ ≤ ((Real.log x)^A)^2 := pow_le_pow_left₀ (Nat.cast_nonneg q) hq 2
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hlog.le]; congr 1; ring
  have hnorm : ((heckeDirichletTwist η χ).modulus.absNorm : ℝ) ≤
      (η.modulus.absNorm : ℝ)*(q : ℝ)^2 := by exact_mod_cast heckeDirichletTwist_modulus_norm η χ
  apply (hnorm.trans (mul_le_mul_of_nonneg_left hq2 (Nat.cast_nonneg _))).trans
  have hpos := Real.rpow_pos_of_pos hx0 δ
  have hh : (η.modulus.absNorm : ℝ)*(Real.log x)^(2*A)/x^δ < 1 := by
    simpa only [mul_div_assoc] using hx
  exact (div_lt_one hpos).mp hh |>.le

theorem heckePrime_frequency_transport {x H B δ : ℝ}
    (hx : 0 < x) (hδ : 0 < δ) (hB : 0 ≤ B) (hH : x^δ ≤ H) :
    x^B ≤ H^(B/δ) := by
  calc
    _ = (x^δ)^(B/δ) := by rw [← Real.rpow_mul hx.le]; congr 1; field_simp
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hH (div_nonneg hB hδ.le)

theorem heckePrime_bin_height_budget {H b t : ℝ}
    (hH : 5 ≤ H) (hb : 0 ≤ b) (ht : |t| ≤ H^b) :
    2 < H^(b+1) ∧ |t|+H^(b+1)/2 ≤ 2*H^(b+1) ∧
      (3+2*H^(b+1))^2 ≤ H^(2*(b+1)+4) := by
  have hH1 : 1 ≤ H := by linarith
  have hHp : 0 < H := by linarith
  have hp : 1 ≤ H^(b+1) := Real.one_le_rpow hH1 (by linarith)
  have hHp1 : H ≤ H^(b+1) := by
    calc
      H = H^(1 : ℝ) := (Real.rpow_one H).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
  have hf : |t| ≤ H^(b+1) := ht.trans
    (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith))
  refine ⟨by linarith, by linarith, ?_⟩
  have hfour : (25 : ℝ) ≤ H^4 := by nlinarith [sq_nonneg (H^2-25)]
  calc
    _ ≤ (5*H^(b+1))^2 := by gcongr; linarith
    _ = 25*(H^(b+1))^2 := by ring
    _ ≤ H^4*(H^(b+1))^2 := mul_le_mul_of_nonneg_right hfour (sq_nonneg _)
    _ = _ := by
      rw [← Real.rpow_natCast H 4, ← Real.rpow_natCast (H^(b+1)) 2,
        ← Real.rpow_mul hHp.le, ← Real.rpow_add hHp]
      congr 1
      ring

end ArtinMatthews
