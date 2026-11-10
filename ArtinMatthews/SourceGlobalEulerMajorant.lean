module

public import ArtinMatthews.SourceGlobalEulerCoefficients
public import ArtinMatthews.ReflectionCoefficientGaussBound
public import ArtinMatthews.SourceEulerNormAlgebra
public import ArtinMatthews.SourceExponentPowers
public import ArtinMatthews.SourcePrimeNormSummability
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Initial absolute convergence of the actual four-ideal source series.
Only the proved coarse bound for the global gamma2 finite sum is used. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

theorem sourcePrimeExponentNorm_cpow_norm (e : SourcePrimeExponents F S₀) (s : ℂ) :
    ‖(sourcePrimeExponentNorm F S₀ e : ℂ) ^ s‖ =
      (sourcePrimeExponentNorm F S₀ e : ℝ) ^ s.re := by
  have hq : 0 < (sourcePrimeExponentNorm F S₀ e : ℝ) :=
    Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ e)
  simpa only [Complex.ofReal_natCast] using Complex.norm_cpow_eq_rpow_re_of_pos hq s

variable [IsTotallyComplex F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)

theorem sourceGlobalEulerTerm_norm_le (u : sourceRing F S₀) (ξ w z : ℂ)
    (a : SourceExponentCoordinates F S₀) :
    ‖sourceGlobalEulerTerm F hζ S₀ hS η u ξ w z a‖ ≤
      sourceCoordinateMajorant F S₀ (ξ.re - 1) (3 * ξ.re - 2) (w.re - 1) (6 * z.re) a := by
  let qc : ℝ := sourcePrimeExponentNorm F S₀ a.1.val
  let qn : ℝ := sourcePrimeExponentNorm F S₀ a.2.1
  let qs : ℝ := sourcePrimeExponentNorm F S₀ a.2.2.1
  let qr : ℝ := sourcePrimeExponentNorm F S₀ a.2.2.2
  have hc : 0 < qc := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ _)
  have hn : 0 < qn := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ _)
  have hs : 0 < qs := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ _)
  have hA : (sourcePrimeExponentNorm F S₀ (a.1.val + 3 • a.2.1) : ℝ) = qc * qn ^ (3 : ℕ) := by
    rw [sourcePrimeExponentNorm_squarefree_cube, Nat.cast_mul, Nat.cast_pow]
  have hΓ := reflectionGammaTwo_norm_le_sqrt F hζ S₀ a.1.val
  have hΘ := reflectionThetaValue_norm_le_one F hζ S₀ hS η (a.1.val + 3 • a.2.1)
  have hF := sourceExponentFiniteF_norm_le F hζ S₀ (reflectionPrimeCharacters F hζ S₀)
    a.2.2.1 (a.1.val + 3 • a.2.1)
    (u * sourcePrimeExponentGenerator F hζ S₀ a.2.2.2 ^ 6)
  rw [hA] at hF
  have hx : (-(1 / 2 : ℂ) - ξ).re = -(1 / 2 : ℝ) - ξ.re := by norm_num [Complex.sub_re]
  have hy : (-1 - 3 * ξ).re = -1 - 3 * ξ.re := by simp [Complex.sub_re, Complex.mul_re]
  have hz : (-(6 : ℂ) * z).re = -6 * z.re := by simp [Complex.mul_re]
  rw [sourceGlobalEulerTerm]
  simp only [norm_mul, sourcePrimeExponentNorm_cpow_norm, Complex.neg_re]
  rw [hx, hy, hz]
  calc
    _ ≤ Real.sqrt qc * 1 * (qs * (qc * qn ^ (3 : ℕ))) * qc ^ (-(1 / 2 : ℝ) - ξ.re) *
        qn ^ (-1 - 3 * ξ.re) * qs ^ (-w.re) * qr ^ (-6 * z.re) := by
      gcongr
    _ = qc ^ (1 - ξ.re) * (qn ^ (2 - 3 * ξ.re) *
        (qs ^ (1 - w.re) * qr ^ (-6 * z.re))) := by
      rw [mul_one]
      exact sourceEulerCoarseMajorant_algebra qc qn qs qr ξ.re w.re z.re hc hn hs
    _ = sourceCoordinateMajorant F S₀ (ξ.re - 1) (3 * ξ.re - 2) (w.re - 1) (6 * z.re) a := by
      simp only [sourceCoordinateMajorant, neg_sub, neg_mul, qc, qn, qs, qr]

theorem sourceGlobalCalF_summable_norm (u : sourceRing F S₀) (ξ w z : ℂ)
    (hξ : 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    Summable (fun a : SourceExponentCoordinates F S₀ =>
      ‖sourceGlobalEulerTerm F hζ S₀ hS η u ξ w z a‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (sourceGlobalEulerTerm_norm_le F S₀ hζ hS η u ξ w z)
    (sourceCoordinateMajorant_summable F S₀ (by linarith) (by linarith) (by linarith) (by linarith))

theorem sourceGlobalCalF_norm_le (u : sourceRing F S₀) (ξ w z : ℂ)
    (hξ : 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    ‖sourceGlobalCalF F hζ S₀ hS η u ξ w z‖ ≤
      ∑' a : SourceExponentCoordinates F S₀,
        sourceCoordinateMajorant F S₀ (ξ.re - 1) (3 * ξ.re - 2) (w.re - 1) (6 * z.re) a := by
  have he := sourceGlobalCalF_summable_norm F S₀ hζ hS η u ξ w z hξ hw hz
  exact (norm_tsum_le_tsum_norm he).trans (he.tsum_le_tsum
    (sourceGlobalEulerTerm_norm_le F S₀ hζ hS η u ξ w z)
    (sourceCoordinateMajorant_summable F S₀ (by linarith) (by linarith) (by linarith) (by linarith)))

end
end ArtinMatthews.SourceEulerAssembly
