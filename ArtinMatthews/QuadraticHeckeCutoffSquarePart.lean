module

public import ArtinMatthews.QuadraticHeckeCutoffSupport
public import ArtinMatthews.SourceQuadraticIdealSquarePart
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


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic UniqueFactorizationMonoid SourceEulerAssembly
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
open HeckeIdealMobius (divisors)

/-- The square part of a cutoff triple divides the common squarefree ideal. -/
theorem quadraticHeckeCutoffProduct_squareParts
    {g h d e : Ideal (𝓞 K)} (hg : Squarefree g)
    (hh : Squarefree h) (hhg : IsCoprime h g) (hd : d ∣ g) (he : e ∣ g) :
    ∃ a r : Ideal (𝓞 K), Squarefree a ∧ r ∣ g ∧ a * r ^ 2 = h * d * e := by
  have hd₀ : d ≠ ⊥ := ne_zero_of_dvd_ne_zero hg.ne_zero hd
  have he₀ : e ≠ ⊥ := ne_zero_of_dvd_ne_zero hg.ne_zero he
  let b : {I : Ideal (𝓞 K) // I ≠ ⊥} :=
    ⟨h * d * e, mul_ne_zero (mul_ne_zero hh.ne_zero hd₀) he₀⟩
  let p := sourceQuadraticIdealSquareParts K b
  have hp : p.1.val * p.2.val ^ 2 = h * d * e := sourceQuadraticIdealSquareParts_val K b
  refine ⟨p.1.val, p.2.val, p.1.property, ?_, hp⟩
  have hsquare : p.2.val * p.2.val ∣ h * (d * e) := by
    refine ⟨p.1.val, ?_⟩
    calc
      h * (d * e) = h * d * e := (mul_assoc h d e).symm
      _ = p.1.val * p.2.val ^ 2 := hp.symm
      _ = (p.2.val * p.2.val) * p.1.val := by rw [pow_two, mul_comm]
  have hrde : p.2.val ∣ d * e := hh.dvd_of_squarefree_of_mul_dvd_mul_right hsquare
  have hhde : IsCoprime h (d * e) :=
    (hhg.of_isCoprime_of_dvd_right hd).mul_right (hhg.of_isCoprime_of_dvd_right he)
  have hrh : IsCoprime p.2.val h := hhde.symm.of_isCoprime_of_dvd_left hrde
  have hsquarede : p.2.val * p.2.val ∣ d * e :=
    (hrh.mul_left hrh).dvd_of_dvd_mul_left hsquare
  apply (pow_dvd_pow_iff_dvd (n := 2) (by decide)).1
  simpa only [pow_two] using hsquarede.trans (mul_dvd_mul hd he)

/-- A nonzero grouped boundary coefficient has a square part dividing `g`. -/
theorem quadraticHeckeCutoffCoefficient_squareParts
    {g b : Ideal (𝓞 K)} {H : ℝ} (hg : Squarefree g)
    (hb : quadraticHeckeCutoffCoefficient K g H b ≠ 0) :
    ∃ a r : Ideal (𝓞 K), Squarefree a ∧ r ∣ g ∧ a * r ^ 2 = b := by
  unfold quadraticHeckeCutoffCoefficient at hb
  obtain ⟨h, hh, hhne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  obtain ⟨d, hd, hdne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hhne
  obtain ⟨e, he, hene⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdne
  have hcond : h * d * e = b ∧ H < (Ideal.absNorm (h * d) : ℝ) := by
    by_contra hc
    exact hene (ite_eq_right hc)
  obtain ⟨ha, _, hcop⟩ := (mem_quadraticHeckeCoprimeCutoff K).1 hh
  rw [← hcond.1]
  exact quadraticHeckeCutoffProduct_squareParts K hg ha hcop
    ((HeckeIdealMobius.mem_divisors K hg.ne_zero).1 hd)
    ((HeckeIdealMobius.mem_divisors K hg.ne_zero).1 he)

/-- The square factor contributes its reciprocal norm under a quadratic character. -/
theorem quadraticHeckeHalfCoefficient_squarePart {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M)
    (hχ : ∀ J : Ideal (𝓞 K), J ≠ ⊥ → IsCoprime J M → ψ.allCoefficient J ^ 2 = 1)
    (a r : Ideal (𝓞 K)) (hr : r ≠ ⊥) (hrM : IsCoprime r M) :
    quadraticHeckeHalfCoefficient K ψ (a * r ^ 2) =
      quadraticHeckeHalfCoefficient K ψ a * (Ideal.absNorm r : ℂ)⁻¹ := by
  have hn : (Ideal.absNorm r : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hr
  have hs : quadraticHeckeHalfCoefficient K ψ r ^ 2 = (Ideal.absNorm r : ℂ)⁻¹ := by
    rw [quadraticHeckeHalfCoefficient_apply, mul_pow, hχ r hr hrM, one_mul, pow_two,
      ← Complex.cpow_add _ _ hn]
    rw [show (-(1 / 2 : ℂ)) + -(1 / 2 : ℂ) = -1 by ring, Complex.cpow_neg_one]
  rw [map_mul, map_pow, hs]

/-- Both the norm annulus and the restricted square part hold for the grouped support. -/
theorem quadraticHeckeCutoffCoefficient_support
    {g b : Ideal (𝓞 K)} {H : ℝ} (hg : Squarefree g)
    (hb : quadraticHeckeCutoffCoefficient K g H b ≠ 0) :
    H < (Ideal.absNorm b : ℝ) ∧
      (Ideal.absNorm b : ℝ) ≤ H * (Ideal.absNorm g : ℝ) ^ 2 ∧
      ∃ a r : Ideal (𝓞 K), Squarefree a ∧ r ∣ g ∧ a * r ^ 2 = b := by
  have hmem : b ∈ quadraticHeckeCutoffAnnulus K g H := by
    by_contra h
    exact hb (quadraticHeckeCutoffCoefficient_eq_zero_of_not_mem K hg h)
  have hn := (mem_quadraticHeckeCutoffAnnulus K).1 hmem
  exact ⟨hn.1, hn.2, quadraticHeckeCutoffCoefficient_squareParts K hg hb⟩

end
end ArtinMatthews
