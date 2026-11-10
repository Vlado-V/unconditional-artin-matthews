module

public import ArtinMatthews.SIntegerSourceFiniteF
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The true finite source sum has its elementary cardinality bound.
The phase modulus-one statement is derived from the actual standard
adelic character, including every finite place in S. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain SIntegerPrincipalization SIntegerQuotient StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]

theorem sourceStandardCharacter_norm (S : Finset (HeightOneSpectrum (𝓞 F))) (x : F) :
    ‖sCharacter F S x‖ = 1 := by
  change ‖rationalCharacter F x * ∏ v ∈ S,
    localFiniteCharacter F v (algebraMap F (v.adicCompletion F) x)‖ = 1
  rw [norm_mul, norm_prod, rationalCharacter_unitary]
  simp only [localFiniteCharacter_unitary, Finset.prod_const_one, mul_one]

theorem sourceFiniteSum_norm_le (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (I J : Ideal (PrincipalIntegerRing S₀))
    [Finite ((PrincipalIntegerRing S₀) ⧸ I)] [Finite ((PrincipalIntegerRing S₀) ⧸ J)]
    (s A h : PrincipalIntegerRing S₀) (f g : PrincipalIntegerRing S₀ → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1) :
    ‖sourceFiniteSum S₀ I J s A h f g‖ ≤
      (Nat.card ((PrincipalIntegerRing S₀) ⧸ I) : ℝ) *
        (Nat.card ((PrincipalIntegerRing S₀) ⧸ J) : ℝ) := by
  let := Fintype.ofFinite ((PrincipalIntegerRing S₀) ⧸ I)
  let := Fintype.ofFinite ((PrincipalIntegerRing S₀) ⧸ J)
  let H (d : (PrincipalIntegerRing S₀) ⧸ I) (v : (PrincipalIntegerRing S₀) ⧸ J) : ℂ :=
    if h - A * Quotient.out d ∈ I then
      f (Quotient.out d) * g (Quotient.out v) *
        sCharacter F (principalizingSet S₀)
          (((h - A * Quotient.out d : PrincipalIntegerRing S₀) : F) *
            (Quotient.out v : PrincipalIntegerRing S₀) / ((s : F) * (A : F))) else 0
  have hH (d : (PrincipalIntegerRing S₀) ⧸ I) (v : (PrincipalIntegerRing S₀) ⧸ J) :
      ‖H d v‖ ≤ 1 := by
    dsimp only [H]
    split_ifs
    · rw [norm_mul, norm_mul, sourceStandardCharacter_norm, mul_one]
      simpa only [mul_one] using
        mul_le_mul (hf (Quotient.out d)) (hg (Quotient.out v))
          (norm_nonneg (g (Quotient.out v))) zero_le_one
    · simp only [norm_zero, zero_le_one]
  change ‖∑' d, ∑' v, H d v‖ ≤ _
  simp only [tsum_fintype]
  calc
    _ ≤ ∑ d, ‖∑ v, H d v‖ := norm_sum_le _ _
    _ ≤ ∑ _d : (PrincipalIntegerRing S₀) ⧸ I,
        ∑ _v : (PrincipalIntegerRing S₀) ⧸ J, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun v _ => hH d v))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Nat.card_eq_fintype_card]

end
end ArtinMatthews
