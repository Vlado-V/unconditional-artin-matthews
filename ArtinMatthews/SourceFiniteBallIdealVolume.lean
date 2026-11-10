module

public import ArtinMatthews.SourceFiniteBallIdeal
public import ArtinMatthews.StandardLocalFourier
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ArtinMatthews.StandardLocalHaarScaling
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
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

/-! The finite S Haar factor is exactly the inverse of the ideal norm
times sqrt(discriminant) in the actual archimedean lattice Poisson law.
The cancellation uses the complete support of the genuine different. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain FractionalIdeal MeasureTheory StandardAdelic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

theorem sourceDifferent_product (hS : traceBadPlaces K ⊆ S) :
    (∏ v : S, v.val.asIdeal ^ sourceDifferentExponent K v.val) = differentIdeal ℤ (𝓞 K) := by
  let f (P : HeightOneSpectrum (𝓞 K)) : Ideal (𝓞 K) := P.asIdeal ^ sourceDifferentExponent K P
  have hf : Function.mulSupport f ⊆ (S : Set (HeightOneSpectrum (𝓞 K))) := by
    intro P hP
    by_contra hn
    apply hP
    change P.asIdeal ^ sourceDifferentExponent K P = 1
    rw [(sourceDifferentExponent_eq_zero_iff K P).mpr (fun h => hn (hS h)), pow_zero]
  change (∏ v : S, f v.val) = _
  rw [Finset.prod_coe_sort, ← finprod_eq_finsetProd_of_mulSupport_subset f hf]
  exact Ideal.finprod_heightOneSpectrum_factorization differentIdeal_ne_bot

theorem sourceDifferent_norm_product (hS : traceBadPlaces K ⊆ S) :
    (∏ v : S, (Ideal.absNorm v.val.asIdeal : ℝ) ^ sourceDifferentExponent K v.val) =
      |(discr K : ℝ)| := by
  have h := congrArg (fun I : Ideal (𝓞 K) => Ideal.absNorm I) (sourceDifferent_product K S hS)
  change Ideal.absNorm (∏ v : S, v.val.asIdeal ^ sourceDifferentExponent K v.val) = _ at h
  rw [map_prod, absNorm_differentIdeal K (𝓞 K)] at h
  simp only [map_pow] at h
  simpa only [Nat.cast_prod, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] using
    congrArg (fun n : ℕ => (n : ℝ)) h

theorem sourceLocalSelfDual_ideal_ball_volume (P : HeightOneSpectrum (𝓞 K)) (e : ℤ) :
    (sourceLocalSelfDual K P).real (sourceLocalBall K P (-e)) =
      ((Ideal.absNorm P.asIdeal : ℝ) ^ e)⁻¹ *
        (Real.sqrt ((Ideal.absNorm P.asIdeal : ℝ) ^ sourceDifferentExponent K P))⁻¹ := by
  let μ := sourceLocalSelfDual K P
  let : μ.IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  let q := (Ideal.absNorm P.asIdeal : ℝ)
  let d := sourceDifferentExponent K P
  have hq : 0 ≤ q := (sourceLocalNorm_pos K P).le
  have hc : μ.real (sourceLocalBall K P 0) = (Real.sqrt (q ^ d))⁻¹ := by
    rw [sourceLocalSelfDual_volume_integer K P]
    change q ^ (-(d : ℝ) / 2) = (Real.sqrt (q ^ d))⁻¹
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast q d, ← Real.rpow_mul hq, ← Real.rpow_neg hq]
    congr 1
    ring
  change μ.real (sourceLocalBall K P (-e)) = (q ^ e)⁻¹ * (Real.sqrt (q ^ d))⁻¹
  rw [sourceLocalBall_volume_scaling K P μ, hc, zpow_neg]

theorem sourceFiniteBallIdeal_volume_product (hS : traceBadPlaces K ⊆ S) (e : S → ℤ) :
    (∏ v : S, (sourceLocalSelfDual K v.val).real (sourceLocalBall K v.val (-(e v)))) =
      1 / ((FractionalIdeal.absNorm (sourceFiniteBallIdeal K S e) : ℝ) * Real.sqrt |(discr K : ℝ)|) := by
  simp_rw [sourceLocalSelfDual_ideal_ball_volume]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib,
    ← sourceFiniteBallIdeal_norm K S e]
  have hs := Real.sqrt_prod (Finset.univ : Finset S)
    (x := fun v : S => (Ideal.absNorm v.val.asIdeal : ℝ) ^ sourceDifferentExponent K v.val)
    (fun v _ => pow_nonneg (sourceLocalNorm_pos K v.val).le _)
  rw [← hs, sourceDifferent_norm_product K S hS, one_div, mul_inv]

end
end ArtinMatthews.SourcePhysical
