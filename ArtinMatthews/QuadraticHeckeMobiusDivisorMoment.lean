module

public import ArtinMatthews.VaryingKummerAnalyticHeckeIdealMobius
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem quadraticHeckeMobiusDivisorMoment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ (σ : ℝ), 1 ≤ σ →
      (∑ d ∈ HeckeIdealMobius.divisors F I,
        ‖(moebius d : ℂ)‖ * (Ideal.absNorm d : ℝ) ^ (σ - 1)) ≤
        C * (Ideal.absNorm I : ℝ) ^ σ := by
  obtain ⟨C, hC, hcard⟩ := HeckeIdealMobius.squarefree_divisor_small_power F 1 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro I hI σ hσ
  let S := HeckeIdealMobius.divisors F I
  have hnorm : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hzero (d : Ideal (𝓞 F)) (hd : ¬ Squarefree d) :
      ‖(moebius d : ℂ)‖ * (Ideal.absNorm d : ℝ) ^ (σ - 1) = 0 := by
    rw [moebius_of_not_squarefree hd, Int.cast_zero, norm_zero, zero_mul]
  have hfilter : (∑ d ∈ S, ‖(moebius d : ℂ)‖ * (Ideal.absNorm d : ℝ) ^ (σ - 1)) =
      ∑ d ∈ S.filter Squarefree, ‖(moebius d : ℂ)‖ * (Ideal.absNorm d : ℝ) ^ (σ - 1) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    exact hzero d (fun h => hnot (Finset.mem_filter.mpr ⟨hd, h⟩))
  change (∑ d ∈ S, _) ≤ _
  rw [hfilter]
  calc
    _ ≤ ∑ _d ∈ S.filter Squarefree, (Ideal.absNorm I : ℝ) ^ (σ - 1) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdiv := (HeckeIdealMobius.mem_divisors F hI).mp (Finset.mem_filter.mp hd).1
      have hnd : Ideal.absNorm d ≤ Ideal.absNorm I :=
        Nat.le_of_dvd (Nat.cast_pos.mp hnorm) (map_dvd Ideal.absNorm hdiv)
      have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (Ideal.absNorm d))
        (show (Ideal.absNorm d : ℝ) ≤ Ideal.absNorm I by exact_mod_cast hnd) (by linarith : 0 ≤ σ - 1)
      exact (mul_le_mul_of_nonneg_right (HeckeIdealMobius.norm_moebius_le_one F d)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans (by simpa only [one_mul] using hpow)
    _ = ((S.filter Squarefree).card : ℝ) * (Ideal.absNorm I : ℝ) ^ (σ - 1) := by simp
    _ ≤ (C * (Ideal.absNorm I : ℝ)) * (Ideal.absNorm I : ℝ) ^ (σ - 1) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hnorm.le _)
      simpa only [Real.rpow_one, S] using hcard I hI
    _ = C * (Ideal.absNorm I : ℝ) ^ σ := by
      rw [mul_assoc]
      congr 1
      calc
        _ = (Ideal.absNorm I : ℝ) ^ ((1 : ℝ) + (σ - 1)) := by
          simpa only [Real.rpow_one] using (Real.rpow_add hnorm 1 (σ - 1)).symm
        _ = _ := by congr 1; ring

end
end ArtinMatthews
