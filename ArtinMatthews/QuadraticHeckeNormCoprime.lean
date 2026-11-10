module

public import ArtinMatthews.VaryingKummerAnalyticHeckeIdealMobius
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.VaryingKummerAnalyticHeckeFiniteEulerAlgebra
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
public import Mathlib.Tactic.Basify
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
open NumberField Set VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]

private def idealMultiplesEquiv (d : Ideal (𝓞 K)) (hd : d ≠ ⊥) :
    Ideal (𝓞 K) ≃ {J : Ideal (𝓞 K) // d ∣ J} :=
  Equiv.ofBijective (fun J => ⟨d * J, dvd_mul_right _ _⟩)
    ⟨fun J L h => mul_left_cancel₀ hd (congrArg Subtype.val h), fun ⟨J, hJ⟩ => by
      obtain ⟨L, hL⟩ := hJ
      exact ⟨L, Subtype.ext hL.symm⟩⟩

private theorem idealDivisor_mask_tsum (d : Ideal (𝓞 K)) (hd : d ≠ ⊥)
    (f : Ideal (𝓞 K) → ℂ) :
    (∑' J, if d ∣ J then f J else 0) = ∑' J, f (d * J) := by
  let g (J : Ideal (𝓞 K)) := if d ∣ J then f J else 0
  have hg : Function.support g ⊆ {J : Ideal (𝓞 K) | d ∣ J} := by
    intro J hJ
    by_contra hdJ
    exact hJ (ite_eq_right hdJ)
  change (∑' J, g J) = _
  rw [← tsum_subtype_eq_of_support_subset hg]
  calc
    _ = ∑' J : Ideal (𝓞 K), g (d * J) :=
      ((idealMultiplesEquiv K d hd).tsum_eq (fun J : {J : Ideal (𝓞 K) // d ∣ J} => g J.val)).symm
    _ = _ := by
      apply tsum_congr
      intro J
      simp only [g, dvd_mul_right, ite_true]

/-- Finite ideal Möbius inversion of a summable norm weight with zero value
on the zero ideal. -/
theorem quadraticHeckeNorm_coprime_tsum (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (f : Ideal (𝓞 K) → ℂ) (hf : Summable f) (hf₀ : f ⊥ = 0) :
    (∑' J, if IsCoprime J m then f J else 0) =
      ∑ d ∈ HeckeIdealMobius.divisors K m, (moebius d : ℂ) * ∑' J, f (d * J) := by
  let D := HeckeIdealMobius.divisors K m
  have hD (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
      D.filter (fun d => d ∣ J) = (HeckeIdealMobius.divisors K J).filter (fun d => d ∣ m) := by
    ext d
    simp only [D, Finset.mem_filter, HeckeIdealMobius.mem_divisors K hm,
      HeckeIdealMobius.mem_divisors K hJ, and_comm]
  have hpoint (J : Ideal (𝓞 K)) : (if IsCoprime J m then f J else 0) =
      ∑ d ∈ D, (moebius d : ℂ) * (if d ∣ J then f J else 0) := by
    by_cases hJ : J = ⊥
    · subst J
      simp [hf₀]
    · have hsum := HeckeIdealMobius.common_divisor_moebius_sum K J m hJ
      rw [← hD J hJ] at hsum
      calc
        _ = (∑ d ∈ D.filter (fun d => d ∣ J), (moebius d : ℂ)) * f J := by
          rw [hsum]
          split_ifs <;> simp
        _ = _ := by
          rw [Finset.sum_mul, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro d _
          split_ifs <;> simp
  have hs (d : Ideal (𝓞 K)) : Summable (fun J => if d ∣ J then f J else 0) := by
    apply hf.norm.of_norm_bounded
    intro J
    split_ifs <;> simp
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun d _ => (hs d).mul_left (moebius d : ℂ))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [tsum_mul_left, idealDivisor_mask_tsum K d]
  intro hd₀
  have hdiv := (HeckeIdealMobius.mem_divisors K hm).1 hd
  obtain ⟨J, hJ⟩ := hdiv
  exact hm (by rw [hJ, hd₀, Ideal.bot_mul])

end
end ArtinMatthews
