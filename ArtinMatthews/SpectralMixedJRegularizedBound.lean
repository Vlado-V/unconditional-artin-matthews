module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralHeatArithmeticKernel
public import ArtinMatthews.SpectralJRegularizedWeight
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralJRegularizedThreeEighths
public import ArtinMatthews.SpectralMixedCuspKloostermanWeil
public import ArtinMatthews.SpectralMixedCuspNormalization
public import ArtinMatthews.SpectralMixedJModulusPower
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

/-! A uniform summable modulus bound for the actual same-sign mixed J
fibre. Both frequencies retain their original signs and native order. -/
noncomputable section
open Set MeasureTheory Complex
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0MixedJRegularizedHeatFibre_uniform_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (m n : ℤ) (hmn : 0 < m*n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ L R : ℝ, 0 ≤ L → 1 ≤ R → ∀ q : Ioi (0 : ℕ),
      ‖gamma0TrueWidthHeatFibre (r*s) (gamma0CuspOneOver s) 1 q n m
        (spectralJRegularizedWeight f L) R‖ ≤ B/(q.val : ℝ)^(9/8 : ℝ) := by
  have hm : m ≠ 0 := by intro h; simp [h] at hmn
  have hn : n ≠ 0 := by intro h; simp [h] at hmn
  have hnm : 0 < n*m := by simpa only [mul_comm] using hmn
  let K : ℝ := Real.sqrt (|cuspFourierFrequency 1 n| * |cuspFourierFrequency 1 m|)
  let W : ℝ := Real.sqrt (r : ℝ)
  have hK : 0 < K := Real.sqrt_pos.mpr (mul_pos
    (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn))
    (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)))
  have hW : 0 < W := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos r))
  obtain ⟨D,hD,hKernel⟩ := spectralJRegularizedHeatKernel_uniform_small f hf hc hp n m hnm
    (K*(2/W)) (by positivity)
  obtain ⟨A,hA,hWeil⟩ := gamma0MixedKloosterman_weil (by norm_num : (0 : ℝ) < 1/8)
  let G : ℝ := (Int.gcd m n : ℝ)^(1/2 : ℝ)
  have hG : 0 ≤ G := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hgcd : 0 < Int.gcd m n := Int.gcd_pos_of_ne_zero_left n hm
  let B : ℝ := ((A*G)*K*D/W^2)*(2*K/W)^(-1/4 : ℝ)
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  intro L R hL hR q
  letI : NeZero q.val := ⟨q.property.ne'⟩
  have hq : 0 < (q.val : ℝ) := Nat.cast_pos.mpr q.property
  have hq1 : 1 ≤ (q.val : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr q.property)
  have hmod : gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) 1 (q.val : ℝ) =
      (q.val : ℝ)*W := by
    simp only [gamma0TrueWidthModulus,gamma0MixedCusp_trueWidth r s hcop,
      gamma0CuspTrueWidth_identity,Nat.cast_one,Real.sqrt_one,mul_one,W]
  have hX : 0 < K*(2/((q.val : ℝ)*W)) := by positivity
  have hXle : K*(2/((q.val : ℝ)*W)) ≤ K*(2/W) := by
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply div_le_div_of_nonneg_left (by norm_num) hW
    exact le_mul_of_one_le_left hW.le hq1
  have hF := hKernel L R _ hL hR hX hXle
  have hS : ‖gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) 1 q.val n m‖ ≤
      (A*G)*(q.val : ℝ)^(5/8 : ℝ) := by
    have hs := hWeil r s q.val hcop m n
    have hg : ((Nat.gcd q.val (Int.gcd m n) : ℕ) : ℝ)^(1/2 : ℝ) ≤ G := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by norm_num)
      exact_mod_cast Nat.gcd_le_right q.val hgcd
    norm_num only [show (1/2 : ℝ)+1/8 = 5/8 by norm_num] at hs
    calc
      _ ≤ A*(q.val : ℝ)^(5/8 : ℝ)*
          ((Nat.gcd q.val (Int.gcd m n) : ℕ) : ℝ)^(1/2 : ℝ) := hs
      _ ≤ A*(q.val : ℝ)^(5/8 : ℝ)*G :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by ring
  change ‖gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) 1 q.val n m*
      ((K/(gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) 1 (q.val : ℝ))^2 : ℝ) : ℂ)*
      spectralABLHeatKernel (spectralJRegularizedWeight f L) R n m
        (K*(2/gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) 1 (q.val : ℝ)))‖ ≤ _
  rw [hmod,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ ((A*G)*(q.val : ℝ)^(5/8 : ℝ))*(K/((q.val : ℝ)*W)^2)*
        (D*(K*(2/((q.val : ℝ)*W)))^(-1/4 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hS (by positivity)) hF
        (norm_nonneg _) (by positivity)
    _ = _ := spectralMixedJ_modulus_power (q.val : ℝ) K W (A*G) D hq hK hW

end ArtinMatthews
