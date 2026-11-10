module

public import ArtinMatthews.MarkedMajorArcCenteredCoefficient
public import ArtinMatthews.MarkedMajorArcCenteredPrefix
public import ArtinMatthews.MarkedMajorArcPrimePowerAbsorption
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! Low-frequency cancellation of the literal centered long coefficient,
after actual principal-term cancellation and actual partial summation. -/
namespace ArtinMatthews
open Finset Filter
open scoped Topology

 theorem marked_major_low_centered_cancellation (a η τ C T P : ℝ)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ)
    (_hC : 0 ≤ C) (hT : 0 ≤ T) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (modulation t H u v : ℝ),
        (q:ℝ) ≤ L^a → |modulation| ≤ L^C → |t| ≤ L^T →
        Real.exp (τ*L) ≤ H → H ≤ u → u ≤ v → v ≤ 2*H → v ≤ Real.exp (η*L) →
        ‖markedMajorCenteredSum χ (Real.exp (L^(6/25:ℝ))) modulation t H u v‖ ≤ L^(-P) := by
  classical
  let F := max T C
  let R := P+F+1
  have hF : 0 ≤ F := hT.trans (le_max_left _ _)
  have hR : 0 ≤ R := by dsimp [R]; linarith
  obtain ⟨K,hK,hprefix⟩ := marked_major_centered_prefix_low a η τ R ha hη hτ hR
  filter_upwards [hprefix,marked_major_prime_power_uniform_power P η τ (1/2) hP hτ hη (by norm_num),
    eventually_ge_atTop (max 1 (max (1/τ) (40*K)))] with L hp hpp hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hKL : 40*K ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hτL : 1 ≤ τ*L := by
    have hh := (div_le_iff₀ hτ).mp ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
    nlinarith
  intro q _ χ modulation t H u v hq hmod ht hH hHu huv hvH hvhi
  let W := Real.exp (L^(6/25:ℝ))
  let D := 4*K*H*L^(-R)
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  have hup : 0 < u := hHp.trans_le hHu
  have hlog : 1 ≤ Real.log u := hτL.trans ((Real.le_log_iff_exp_le hup).mpr (hH.trans hHu))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hinterval (w : ℝ) (hw : w ∈ Set.Icc u v) :
      ‖∑ n ∈ Ioc ⌊u⌋₊ ⌊w⌋₊, markedCenteredMangoldt χ W n‖ ≤ D := by
    have hpw := hp q χ w hq (hH.trans (hHu.trans hw.1)) (hw.2.trans hvhi)
    have hpu := hp q χ u hq (hH.trans hHu) (huv.trans hvhi)
    have hs := sum_Ioc_consecutive (markedCenteredMangoldt χ W)
      (Nat.zero_le ⌊u⌋₊) (Nat.floor_mono hw.1)
    have he : (∑ n ∈ Ioc ⌊u⌋₊ ⌊w⌋₊, markedCenteredMangoldt χ W n) =
        (∑ n ∈ Ioc 0 ⌊w⌋₊, markedCenteredMangoldt χ W n)-
          (∑ n ∈ Ioc 0 ⌊u⌋₊, markedCenteredMangoldt χ W n) := by linear_combination hs
    rw [he]
    calc
      _ ≤ ‖∑ n ∈ Ioc 0 ⌊w⌋₊, markedCenteredMangoldt χ W n‖+
        ‖∑ n ∈ Ioc 0 ⌊u⌋₊, markedCenteredMangoldt χ W n‖ := norm_sub_le _ _
      _ ≤ K*w*L^(-R)+K*u*L^(-R) := add_le_add hpw hpu
      _ ≤ D := by
        dsimp [D]
        have huw : u+w ≤ 4*H := by linarith [hw.1,hw.2]
        nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huw hK.le)
          (Real.rpow_nonneg hLp.le (-R))]
  have hb := marked_centered_prefix_partial_summation χ W modulation t H hHp hHu huv hvH hlog hD hinterval
  have hfreq : |t+modulation|+3 ≤ 5*L^F := by
    have hTf := (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left T C))
    have hCf := (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right T C))
    have hLf : 1 ≤ L^F := Real.one_le_rpow hL1 hF
    linarith [abs_add_le t modulation]
  have hmain : (D/H)*(|t+modulation|+3) ≤ (1/2)*L^(-P) := by
    have hDH : D/H = 4*K*L^(-R) := by dsimp [D]; field_simp
    rw [hDH]
    calc
      _ ≤ (4*K*L^(-R))*(5*L^F) := mul_le_mul_of_nonneg_left hfreq (by positivity)
      _ = L^(-P)*(20*K/L) := by
        have he : -R+F = -P+(-1) := by dsimp [R]; ring
        rw [show (4*K*L^(-R))*(5*L^F) = 20*K*(L^(-R)*L^F) by ring,
          ← Real.rpow_add hLp,he,Real.rpow_add hLp,Real.rpow_neg_one]
        ring
      _ ≤ L^(-P)*(1/2) := mul_le_mul_of_nonneg_left
        ((div_le_iff₀ hLp).mpr (by linarith)) (Real.rpow_nonneg hLp.le _)
      _ = _ := mul_comm _ _
  have hpower := hpp H v hH (hHu.trans huv) hvH hvhi
  exact hb.trans (by linarith)

end ArtinMatthews
