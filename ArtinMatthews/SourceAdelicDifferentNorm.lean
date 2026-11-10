module

public import ArtinMatthews.SourceAdelicStandardHaar
public import ArtinMatthews.StandardLocalDifferent
public import ArtinMatthews.StandardLocalFourier
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

/-! The actual finite local self-dual integer masses multiply to the inverse
square root of the absolute discriminant. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical Function
open scoped NumberField AdeleRing Topology Classical ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def sourceKPDifferentNormFactor (P : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (Ideal.absNorm P.asIdeal : ℝ) ^ sourceDifferentExponent K P

theorem sourceKPDifferentNormFactor_pos (P : HeightOneSpectrum (𝓞 K)) :
    0 < sourceKPDifferentNormFactor K P := pow_pos (sourceLocalNorm_pos K P) _

theorem sourceKPDifferentNormFactor_support :
    HasFiniteMulSupport (sourceKPDifferentNormFactor K) := by
  let D := differentIdeal ℤ (𝓞 K)
  have hD : D ≠ 0 := differentIdeal_ne_bot
  have hf := Ideal.hasFiniteMulSupport hD
  apply hf.subset
  intro P hP hzero
  apply hP
  have h := congrArg (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ)) hzero
  simpa [sourceKPDifferentNormFactor, HeightOneSpectrum.maxPowDividing,
    sourceDifferentExponent, map_pow, D] using h

theorem sourceKPDifferentNormFactor_product :
    (∏ᶠ P : HeightOneSpectrum (𝓞 K), sourceKPDifferentNormFactor K P) =
      |(discr K : ℝ)| := by
  let D := differentIdeal ℤ (𝓞 K)
  have hD : D ≠ 0 := differentIdeal_ne_bot
  let m : Ideal (𝓞 K) →* ℝ := (Nat.castRingHom ℝ).toMonoidHom.comp Ideal.absNorm.toMonoidHom
  calc
    _ = ∏ᶠ P : HeightOneSpectrum (𝓞 K), m (P.maxPowDividing D) := by
      apply finprod_congr
      intro P
      simp [m, D, sourceKPDifferentNormFactor, HeightOneSpectrum.maxPowDividing,
        sourceDifferentExponent, map_pow]
    _ = m (∏ᶠ P : HeightOneSpectrum (𝓞 K), P.maxPowDividing D) :=
      (m.map_finprod (Ideal.hasFiniteMulSupport hD)).symm
    _ = m D := congrArg m (Ideal.finprod_heightOneSpectrum_factorization hD)
    _ = _ := by
      simp [m, D, NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]

theorem sourceKPLocalSelfDual_integer_real (P : HeightOneSpectrum (𝓞 K)) :
    (sourceLocalSelfDual K P).real (P.adicCompletionIntegers K) =
      (sourceKPDifferentNormFactor K P) ^ (-(1 : ℝ) / 2) := by
  rw [← sourceLocalBall_zero K P, sourceLocalSelfDual_volume_integer K P]
  rw [sourceKPDifferentNormFactor, ← Real.rpow_natCast,
    ← Real.rpow_mul (sourceLocalNorm_pos K P).le]
  congr 1
  ring

theorem sourceKPLocalSelfDual_integer_real_support :
    HasFiniteMulSupport (fun P : HeightOneSpectrum (𝓞 K) =>
      (sourceLocalSelfDual K P).real (P.adicCompletionIntegers K)) := by
  apply (sourceKPDifferentNormFactor_support K).subset
  intro P hP hzero
  apply hP
  change (sourceLocalSelfDual K P).real (P.adicCompletionIntegers K) = 1
  rw [sourceKPLocalSelfDual_integer_real, hzero, Real.one_rpow]

theorem sourceKPLocalSelfDual_integer_real_product :
    (∏ᶠ P : HeightOneSpectrum (𝓞 K),
      (sourceLocalSelfDual K P).real (P.adicCompletionIntegers K)) =
      |(discr K : ℝ)| ^ (-(1 : ℝ) / 2) := by
  let f := sourceKPDifferentNormFactor K
  let hf := sourceKPDifferentNormFactor_support K
  have hsupport : Function.mulSupport (fun P => (sourceLocalSelfDual K P).real
      (P.adicCompletionIntegers K)) ⊆ hf.toFinset := by
    intro P hP
    apply hf.mem_toFinset.mpr
    intro hzero
    apply hP
    change (sourceLocalSelfDual K P).real (P.adicCompletionIntegers K) = 1
    rw [sourceKPLocalSelfDual_integer_real, hzero, Real.one_rpow]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupport]
  simp_rw [sourceKPLocalSelfDual_integer_real]
  rw [Real.finsetProd_rpow _ _ (fun P _ => (sourceKPDifferentNormFactor_pos K P).le),
    ← finprod_eq_prod_of_mulSupport_toFinset_subset _ hf (Finset.Subset.refl _),
    sourceKPDifferentNormFactor_product]

theorem sourceKPLocalSelfDual_integer_product :
    (∏ᶠ P : HeightOneSpectrum (𝓞 K),
      sourceLocalSelfDual K P (P.adicCompletionIntegers K)) =
      (sourceKPDiscriminantRoot K)⁻¹ := by
  have hfinite (P : HeightOneSpectrum (𝓞 K)) :
      sourceLocalSelfDual K P (P.adicCompletionIntegers K) ≠ ∞ := by
    let : (sourceLocalSelfDual K P).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
    rw [← sourceLocalBall_zero K P]
    exact (sourceLocalBall_isCompact K P 0).measure_ne_top
  have he (P : HeightOneSpectrum (𝓞 K)) :
      sourceLocalSelfDual K P (P.adicCompletionIntegers K) =
      ENNReal.ofReal ((sourceLocalSelfDual K P).real (P.adicCompletionIntegers K)) := by
    exact (ENNReal.ofReal_toReal (hfinite P)).symm
  have hp := sourceKPLocalSelfDual_integer_real_product K
  have hmap : (∏ᶠ P : HeightOneSpectrum (𝓞 K),
      ENNReal.ofReal ((sourceLocalSelfDual K P).real (P.adicCompletionIntegers K))) =
      ENNReal.ofReal (∏ᶠ P : HeightOneSpectrum (𝓞 K),
        (sourceLocalSelfDual K P).real (P.adicCompletionIntegers K)) := by
    let hf := sourceKPLocalSelfDual_integer_real_support K
    rw [finprod_eq_prod_of_mulSupport_toFinset_subset _ hf (Finset.Subset.refl _)]
    rw [finprod_eq_prod_of_mulSupport_subset _ (show Function.mulSupport (fun P =>
      ENNReal.ofReal ((sourceLocalSelfDual K P).real (P.adicCompletionIntegers K))) ⊆ hf.toFinset from by
      intro P hP
      apply hf.mem_toFinset.mpr
      intro hzero
      apply hP
      dsimp only at hzero ⊢
      rw [hzero, ENNReal.ofReal_one])]
    exact (ENNReal.ofReal_prod_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)).symm
  simp_rw [he]
  have hsqrt : |(discr K : ℝ)| ^ (-(1 : ℝ) / 2) = (Real.sqrt |(discr K : ℝ)|)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (abs_nonneg _)]
    congr 1
    ring
  rw [hmap, hp, hsqrt,
    ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.2 (abs_pos.mpr (by exact_mod_cast discr_ne_zero K)))]
  congr 1
  have hr : (NNReal.sqrt ‖discr K‖₊ : ℝ) = Real.sqrt |(discr K : ℝ)| := by
    rw [Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  rw [← hr, ENNReal.ofReal_coe_nnreal]
  rfl

end
end ArtinMatthews
