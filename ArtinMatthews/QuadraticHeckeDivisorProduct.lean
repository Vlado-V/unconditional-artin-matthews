module

public import ArtinMatthews.VaryingKummerAnalyticHeckeIdealMobius
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
open HeckeIdealMobius (divisors)

/-- A divisor of the first modulus is the exact gcd of a coprime product with that modulus. -/
theorem quadraticHecke_coprime_divisor_gcd {B h d : Ideal (𝓞 F)}
    (hh : IsCoprime h B) (hd : d ∣ B) : gcd (h * d) B = d := by
  obtain ⟨j, hj⟩ := hd
  have hc := hh.of_isCoprime_of_dvd_right
    (show j ∣ B by rw [hj]; exact dvd_mul_left _ _)
  rw [Ideal.isCoprime_iff_gcd] at hc
  rw [hj, mul_comm h d, gcd_mul_left, normalize_eq, hc, mul_one]

/-- The finite divisor sum of a coprime product splits into its unique pair of divisors. -/
theorem quadraticHeckeDivisors_coprime_product_sum
    (B G : Ideal (𝓞 F)) (hB : B ≠ ⊥) (hG : G ≠ ⊥) (hBG : IsCoprime B G)
    (f : Ideal (𝓞 F) → ℂ) :
    (∑ d ∈ divisors F (B * G), f d) =
      ∑ u ∈ divisors F B, ∑ v ∈ divisors F G, f (u * v) := by
  symm
  rw [← Finset.sum_product' (divisors F B) (divisors F G) (fun u v => f (u * v))]
  apply Finset.sum_bij (fun p _ => p.1 * p.2)
  · intro p hp
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
    exact (HeckeIdealMobius.mem_divisors F (mul_ne_zero hB hG)).2
      (mul_dvd_mul ((HeckeIdealMobius.mem_divisors F hB).1 hu)
        ((HeckeIdealMobius.mem_divisors F hG).1 hv))
  · intro p hp q hq heq
    obtain ⟨hpu, hpv⟩ := Finset.mem_product.mp hp
    obtain ⟨hqu, hqv⟩ := Finset.mem_product.mp hq
    have hpu' := (HeckeIdealMobius.mem_divisors F hB).1 hpu
    have hpv' := (HeckeIdealMobius.mem_divisors F hG).1 hpv
    have hqu' := (HeckeIdealMobius.mem_divisors F hB).1 hqu
    have hqv' := (HeckeIdealMobius.mem_divisors F hG).1 hqv
    have hu : p.1 = q.1 := by
      have hpG := hBG.symm.of_isCoprime_of_dvd_left hpv'
      have hqG := hBG.symm.of_isCoprime_of_dvd_left hqv'
      have hpD := quadraticHecke_coprime_divisor_gcd F hpG hpu'
      have hqD := quadraticHecke_coprime_divisor_gcd F hqG hqu'
      rw [mul_comm p.2 p.1] at hpD
      rw [mul_comm q.2 q.1] at hqD
      rw [heq] at hpD
      exact hpD.symm.trans hqD
    have hp0 : p.1 ≠ ⊥ := ne_zero_of_dvd_ne_zero hB hpu'
    exact Prod.ext hu (mul_left_cancel₀ hp0 (by simpa only [hu] using heq))
  · intro d hd
    obtain ⟨u, v, hu, hv, huv⟩ := exists_dvd_and_dvd_of_dvd_mul
      ((HeckeIdealMobius.mem_divisors F (mul_ne_zero hB hG)).1 hd)
    refine ⟨(u, v), Finset.mem_product.mpr ⟨?_, ?_⟩, huv.symm⟩
    · exact (HeckeIdealMobius.mem_divisors F hB).2 hu
    · exact (HeckeIdealMobius.mem_divisors F hG).2 hv
  · intro p _
    rfl

/-- The literal Möbius and multiplicative weights split with the coprime divisors. -/
theorem quadraticHeckeDivisors_coprime_weighted_sum
    (B G : Ideal (𝓞 F)) (hB : B ≠ ⊥) (hG : G ≠ ⊥) (hBG : IsCoprime B G)
    (A : Ideal (𝓞 F) →*₀ ℂ) (f : Ideal (𝓞 F) → ℂ) :
    (∑ d ∈ divisors F (B * G), (moebius d : ℂ) * A d * f d) =
      ∑ u ∈ divisors F B, ∑ v ∈ divisors F G,
        ((moebius u : ℂ) * A u) * ((moebius v : ℂ) * A v) * f (u * v) := by
  rw [quadraticHeckeDivisors_coprime_product_sum F B G hB hG hBG]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have hc := (hBG.of_isCoprime_of_dvd_left ((HeckeIdealMobius.mem_divisors F hB).1 hu)).of_isCoprime_of_dvd_right
    ((HeckeIdealMobius.mem_divisors F hG).1 hv)
  rw [hc.isRelPrime.moebius_mul, Int.cast_mul, map_mul]
  ring

end
end ArtinMatthews
