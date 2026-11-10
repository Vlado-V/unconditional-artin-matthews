module

public import ArtinMatthews.SLocalNormAlgebra
public import ArtinMatthews.SIntegerExteriorGenerator
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
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
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The literal S-product norm of an exterior prime generator is its
actual ideal norm. The local valuations come from the ideal equation,
and the equality is the genuine number-field product formula. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SUnitGroup FractionalIdeal SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem fieldSNorm_eq_product (S : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    fieldSNorm K S a = (∏ w : InfinitePlace K, w (a : K) ^ w.mult) *
      ∏ v ∈ S, HeightOneSpectrum.adicAbv K v (a : K) := by
  rw [show fieldSNorm K S a = sLocalNorm K S (sWholeDiagonal K S a) from rfl,
    sLocalNorm_eq_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro w _
    have hw := InfiniteIdeleGroup.norm_infiniteComponent_principalIdele a w
    exact congrArg (fun x : ℝ => x ^ w.mult) hw
  · calc
      _ = ∏ v : S, HeightOneSpectrum.adicAbv K v.1 (a : K) := by
        apply Finset.prod_congr rfl
        intro v _
        exact FinitePlace.norm_embedding v.1 (a : K)
      _ = _ := Finset.prod_coe_sort S (fun v => HeightOneSpectrum.adicAbv K v (a : K))

private theorem fieldSNorm_prime_of_valuations
    (S : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ S)
    (a : Kˣ) (haP : P.valuation K (a : K) = WithZero.exp (-1 : ℤ))
    (haQ : ∀ Q : HeightOneSpectrum (𝓞 K), Q ∉ S → Q ≠ P → Q.valuation K (a : K) = 1) :
    fieldSNorm K S a = Ideal.absNorm P.asIdeal := by
  have hpNorm : HeightOneSpectrum.adicAbv K P (a : K) = (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
    rw [HeightOneSpectrum.adicAbv_def, haP,
      WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp]
    simp only [zpow_neg, zpow_one, NNReal.coe_inv]
    rfl
  have houtside : ∀ Q : HeightOneSpectrum (𝓞 K), Q ∉ insert P S →
      HeightOneSpectrum.adicAbv K Q (a : K) = 1 := by
    intro Q hQ
    have hQS : Q ∉ S := fun h => hQ (Finset.mem_insert_of_mem h)
    have hQP : Q ≠ P := fun h => hQ (by simp only [h, Finset.mem_insert, true_or])
    simp only [HeightOneSpectrum.adicAbv_def, haQ Q hQS hQP, map_one, NNReal.coe_one]
  have hfinite : (∏ᶠ w : FinitePlace K, w (a : K)) =
      (∏ v ∈ S, HeightOneSpectrum.adicAbv K v (a : K)) *
        (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    simp_rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
    rw [finprod_eq_prod_of_mulSupport_subset (s := insert P S) _ (by
      intro Q hQ
      by_contra hnot
      exact hQ (houtside Q hnot)), Finset.prod_insert hP, hpNorm, mul_comm]
  have hformula := NumberField.prod_abs_eq_one a.ne_zero
  rw [hfinite, ← mul_assoc, ← fieldSNorm_eq_product K S a] at hformula
  have hp0 : (Ideal.absNorm P.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)
  exact (mul_inv_eq_one₀ hp0).mp hformula

theorem fieldSNorm_exterior_prime_generator
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    fieldSNorm K (principalizingSet S₀)
      (Units.mk0 (a : K) (by
        exact Subtype.coe_injective.ne (exterior_generator_ne_zero S₀ P a ha))) =
      Ideal.absNorm P.asIdeal := by
  apply fieldSNorm_prime_of_valuations K _ P hP
  · exact exterior_generator_valuation S₀ P hP a ha
  · exact exterior_generator_other_valuation S₀ P a ha

end
end ArtinMatthews
