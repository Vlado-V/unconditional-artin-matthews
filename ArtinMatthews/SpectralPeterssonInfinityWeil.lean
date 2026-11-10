module

public import ArtinMatthews.SpectralPeterssonLiftedKloosterman
public import ArtinMatthews.SpectralTrueWidthKloosterman
public import ArtinMatthews.AtkinLehnerMixedWeight
public import ArtinMatthews.KloostermanAllModulusWeil
public import ArtinMatthews.SpectralCuspWidthRefinement
public import ArtinMatthews.SpectralPeterssonInfinityRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! Exact true-width arithmetic and the uniform fixed-left-frequency bound. -/

noncomputable section
open Matrix OAI.Erdos970.ErdosKloosterman
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

theorem gamma0CuspTrueWidth_infinity (N : ℕ) [NeZero N] :
    gamma0CuspTrueWidth N (1 : SL(2, ℤ)) = 1 := by
  apply le_antisymm _ (gamma0CuspTrueWidth_pos N 1)
  apply gamma0CuspTrueWidth_minimal N 1 1 (by decide)
  change (N : ℤ) ∣ (1 : ℤ) * ((1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0)^2
  simp

theorem gamma0CuspFrequencyStep_infinity (N : ℕ) [NeZero N] :
    gamma0CuspFrequencyStep N (1 : SL(2, ℤ)) = N := by
  simp [gamma0CuspFrequencyStep, gamma0CuspTrueWidth_infinity]

theorem gamma0TrueWidthKloostermanSum_leftInfinity_lifted (N : ℕ) [NeZero N]
    (b : SL(2, ℤ)) (c : ℕ) [NeZero c] (n m : ℤ) :
    gamma0TrueWidthKloostermanSum N b 1 c n m =
      (gamma0CuspFrequencyStep N b : ℂ)⁻¹ *
        peterssonLiftedKloostermanSum N c (b 0 0) (b 1 0) ((gamma0CuspFrequencyStep N b : ℤ) * n) m := by
  have h := gamma0PeriodKloostermanSum_trueWidth N b 1 c n m
  rw [gamma0CuspFrequencyStep_infinity, gamma0PeriodKloostermanSum_leftInfinity_lifted] at h
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hstep : (gamma0CuspFrequencyStep N b : ℂ) ≠ 0 := by
    exact_mod_cast (gamma0CuspFrequencyStep_pos N b).ne'
  have he :
      peterssonLiftedKloostermanSum N c (b 0 0) (b 1 0) ((gamma0CuspFrequencyStep N b : ℤ) * n) m =
        (gamma0CuspFrequencyStep N b : ℂ) * gamma0TrueWidthKloostermanSum N b 1 c n m := by
    apply mul_left_cancel₀ hN
    simpa only [mul_assoc] using h
  rw [he, ← mul_assoc, inv_mul_cancel₀ hstep, one_mul]

theorem gamma0TrueWidthKloostermanSum_leftInfinity_eq_standardSum (N : ℕ) [NeZero N]
    (b : SL(2, ℤ)) (c : ℕ) [NeZero c] (n m : ℤ) :
    gamma0TrueWidthKloostermanSum N b 1 c n m =
      (gamma0CuspFrequencyStep N b : ℂ)⁻¹ *
        ∑ k : Fin N,
          let H := peterssonLiftedFrequency c (b 1 0) ((gamma0CuspFrequencyStep N b : ℤ) * n) k
          if (N : ℤ) ∣ H then
            atkinPhase ((k.val : ℝ) * c * b 0 0 / N) * standardSum c m (H / (N : ℤ))
          else 0 := by
  rw [gamma0TrueWidthKloostermanSum_leftInfinity_lifted,
    peterssonLiftedKloostermanSum_eq_standardSum]

theorem gamma0TrueWidthKloostermanSum_leftInfinity_weil (N : ℕ) [NeZero N]
    (b : SL(2, ℤ)) (m : ℕ+) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ) [NeZero c] (n : ℤ),
      ‖gamma0TrueWidthKloostermanSum N b 1 c n (m : ℤ)‖ ≤ C * (c : ℝ)^((1/2 : ℝ) + ε) := by
  obtain ⟨C, hC, hweil⟩ := standardKloosterman_weil_bound hε
  have hstep : ‖(gamma0CuspFrequencyStep N b : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast gamma0CuspFrequencyStep_pos N b)
  have hm : 0 < ((m : ℕ) : ℝ) := by exact_mod_cast m.pos
  have hN : 0 < (N : ℝ) := by exact_mod_cast NeZero.pos N
  refine ⟨(N : ℝ) * C * ((m : ℕ) : ℝ)^(1/2 : ℝ),
    mul_pos (mul_pos hN hC) (Real.rpow_pos_of_pos hm _), ?_⟩
  intro c _ n
  let H (k : Fin N) := peterssonLiftedFrequency c (b 1 0) ((gamma0CuspFrequencyStep N b : ℤ) * n) k
  let F (k : Fin N) : ℂ := if (N : ℤ) ∣ H k then
    atkinPhase ((k.val : ℝ) * c * b 0 0 / N) * standardSum c (m : ℤ) (H k / (N : ℤ))
    else 0
  have hstandard (t : ℤ) :
      ‖standardSum c (m : ℤ) t‖ ≤ C * (c : ℝ)^((1/2 : ℝ) + ε) * ((m : ℕ) : ℝ)^(1/2 : ℝ) := by
    have hdvd : Nat.gcd c (Int.gcd (m : ℤ) t) ∣ (m : ℕ) := by
      exact dvd_trans (Nat.gcd_dvd_right _ _)
        (Int.natCast_dvd_natCast.mp (Int.gcd_dvd_left (m : ℤ) t))
    have hg := Nat.le_of_dvd m.pos hdvd
    refine (hweil c (m : ℤ) t).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hg) (by norm_num)
  rw [gamma0TrueWidthKloostermanSum_leftInfinity_eq_standardSum, norm_mul]
  change ‖(gamma0CuspFrequencyStep N b : ℂ)⁻¹‖ * ‖∑ k : Fin N, F k‖ ≤ _
  calc
    _ ≤ ‖∑ k : Fin N, F k‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hstep (norm_nonneg (∑ k : Fin N, F k))
    _ ≤ ∑ k : Fin N, ‖F k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin N, C * (c : ℝ)^((1/2 : ℝ) + ε) * ((m : ℕ) : ℝ)^(1/2 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      dsimp only [F]
      by_cases hd : (N : ℤ) ∣ H k
      · rw [ite_eq_left hd, norm_mul, atkinPhase_norm, one_mul]
        exact hstandard _
      · rw [ite_eq_right hd, norm_zero]
        positivity
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end ArtinMatthews
