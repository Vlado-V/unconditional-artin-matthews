module

public import ArtinMatthews.StandardAdelicLocalNontrivial
public import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! The actual different exponent at every finite prime. Its negative
is the trace-dual fractional ideal count, and the corresponding actual
one-prime pole ideal is contained in the global codifferent. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain FractionalIdeal StandardAdelic
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def sourceDifferentExponent (P : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (Associates.mk P.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 K))).factors

theorem sourceDifferent_le_primePower (P : HeightOneSpectrum (𝓞 K)) :
    differentIdeal ℤ (𝓞 K) ≤ P.asIdeal ^ sourceDifferentExponent K P := by
  apply Ideal.le_of_dvd
  change P.maxPowDividing (differentIdeal ℤ (𝓞 K)) ∣ differentIdeal ℤ (𝓞 K)
  have hD : differentIdeal ℤ (𝓞 K) ≠ 0 := differentIdeal_ne_bot
  calc
    _ ∣ ∏ᶠ Q : HeightOneSpectrum (𝓞 K), Q.maxPowDividing (differentIdeal ℤ (𝓞 K)) :=
      finprod_mem_dvd P (Ideal.hasFiniteMulSupport hD)
    _ = _ := Ideal.finprod_heightOneSpectrum_factorization hD

theorem sourceCodifferent_eq_inv_different :
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) =
      ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]

theorem sourceCodifferent_count (P : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K P (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) =
      -(sourceDifferentExponent K P : ℤ) := by
  rw [sourceCodifferent_eq_inv_different K, FractionalIdeal.count_inv,
    FractionalIdeal.count_coe K P differentIdeal_ne_bot]
  rfl

theorem sourceDifferentExponent_eq_zero_iff (P : HeightOneSpectrum (𝓞 K)) :
    sourceDifferentExponent K P = 0 ↔ P ∉ traceBadPlaces K := by
  simp only [mem_traceBadPlaces, sourceCodifferent_count K P, not_not, neg_eq_zero, Int.natCast_eq_zero]

theorem sourcePoleIdeal_le_codifferent (P : HeightOneSpectrum (𝓞 K)) :
    poleIdeal K P (sourceDifferentExponent K P) ≤
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [poleIdeal, ← FractionalIdeal.coeIdeal_pow, sourceCodifferent_eq_inv_different K]
  apply FractionalIdeal.inv_anti_mono
  · exact FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot
  · exact FractionalIdeal.coeIdeal_ne_zero.mpr (pow_ne_zero _ P.ne_bot)
  · exact (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr (sourceDifferent_le_primePower K P)

end
end ArtinMatthews.SourcePhysical
