module

public import ArtinMatthews.QuadraticHeckeCutoffSplit
public import ArtinMatthews.QuadraticHeckeMainTermEuler
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
open HeckeIdealMobius (divisors)

private theorem divisors_one : divisors K (1 : Ideal (𝓞 K)) = {1} := by
  ext d
  simp only [HeckeIdealMobius.mem_divisors K one_ne_zero, Finset.mem_singleton]
  rw [← isUnit_iff_dvd_one, Ideal.isUnit_iff, Ideal.one_eq_top]

/-- The two finite local factors cancel to the coprime density. -/
theorem quadraticHeckeMainTermEuler_self {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M)
    (hχ : ∀ J : Ideal (𝓞 K), J ≠ ⊥ → IsCoprime J M → ψ.allCoefficient J ^ 2 = 1)
    (g : Ideal (𝓞 K)) (hg : Squarefree g) (hgM : IsCoprime g M) :
    (∑ d ∈ divisors K g, ∑ e ∈ divisors K g,
      (moebius e : ℂ) * quadraticHeckeHalfCoefficient K ψ (d * e)) =
        quadraticHeckeCoprimeDensity K g := by
  have h := quadraticHeckeMainTermEuler K ψ hχ g 1 hg one_ne_zero
    (isCoprime_one_right) hgM
  rw [mul_one, divisors_one K, Finset.sum_singleton] at h
  simpa only [map_one, moebius_one, Int.cast_one, mul_one] using h

/-- Exact finite-cutoff cancellation in the quadratic main term. -/
theorem quadraticHeckeMainTerm_cutoffCancellation {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M)
    (hχ : ∀ J : Ideal (𝓞 K), J ≠ ⊥ → IsCoprime J M → ψ.allCoefficient J ^ 2 = 1)
    (g : Ideal (𝓞 K)) (hg : Squarefree g) (hgM : IsCoprime g M) (H : ℝ) :
    (∑ a ∈ quadraticHeckeSquarefreeCutoff K H, quadraticHeckeHalfCoefficient K ψ a) *
        (∑ e ∈ divisors K g, (moebius e : ℂ) * quadraticHeckeHalfCoefficient K ψ e) -
      (∑ h ∈ quadraticHeckeCoprimeCutoff K g H, quadraticHeckeHalfCoefficient K ψ h) *
        quadraticHeckeCoprimeDensity K g =
      ∑ h ∈ quadraticHeckeCoprimeCutoff K g H, ∑ d ∈ divisors K g,
        ∑ e ∈ divisors K g,
          ((if (Ideal.absNorm (h * d) : ℝ) ≤ H then (1 : ℂ) else 0) - 1) *
            (moebius e : ℂ) * quadraticHeckeHalfCoefficient K ψ (h * d * e) := by
  let A := quadraticHeckeHalfCoefficient K ψ
  have heuler := quadraticHeckeMainTermEuler_self K ψ hχ g hg hgM
  have hlocal (h : Ideal (𝓞 K)) :
      A h * quadraticHeckeCoprimeDensity K g =
        ∑ d ∈ divisors K g, ∑ e ∈ divisors K g, (moebius e : ℂ) * A (h * d * e) := by
    rw [← heuler, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [A, map_mul]
    ring
  change (∑ a ∈ quadraticHeckeSquarefreeCutoff K H, A a) *
      (∑ e ∈ divisors K g, (moebius e : ℂ) * A e) -
    (∑ h ∈ quadraticHeckeCoprimeCutoff K g H, A h) * quadraticHeckeCoprimeDensity K g = _
  rw [quadraticHeckeSquarefreeCutoff_split K g hg H A]
  simp only [Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [hlocal h, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hc : (Ideal.absNorm (h * d) : ℝ) ≤ H
  · simp only [hc, ite_true, sub_self, zero_mul, sub_eq_zero]
    simp only [A, map_mul]
    ring
  · simp only [hc, ite_false, zero_mul, zero_sub, neg_mul, one_mul]
    rfl

/-- The cutoff discrepancy is the sum of the omitted product terms. -/
theorem quadraticHeckeMainTerm_cutoffTail {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M)
    (hχ : ∀ J : Ideal (𝓞 K), J ≠ ⊥ → IsCoprime J M → ψ.allCoefficient J ^ 2 = 1)
    (g : Ideal (𝓞 K)) (hg : Squarefree g) (hgM : IsCoprime g M) (H : ℝ) :
    (∑ a ∈ quadraticHeckeSquarefreeCutoff K H, quadraticHeckeHalfCoefficient K ψ a) *
        (∑ e ∈ divisors K g, (moebius e : ℂ) * quadraticHeckeHalfCoefficient K ψ e) -
      (∑ h ∈ quadraticHeckeCoprimeCutoff K g H, quadraticHeckeHalfCoefficient K ψ h) *
        quadraticHeckeCoprimeDensity K g =
      ∑ h ∈ quadraticHeckeCoprimeCutoff K g H, ∑ d ∈ divisors K g,
        ∑ e ∈ divisors K g,
          if H < (Ideal.absNorm (h * d) : ℝ) then
            -(moebius e : ℂ) * quadraticHeckeHalfCoefficient K ψ (h * d * e) else 0 := by
  rw [quadraticHeckeMainTerm_cutoffCancellation K ψ hχ g hg hgM H]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  by_cases hc : (Ideal.absNorm (h * d) : ℝ) ≤ H
  · rw [ite_eq_left hc, ite_eq_right (not_lt.mpr hc)]
    simp only [sub_self, zero_mul]
  · rw [ite_eq_right hc, ite_eq_left (lt_of_not_ge hc)]
    simp only [zero_sub, neg_mul, one_mul]

end
end ArtinMatthews
