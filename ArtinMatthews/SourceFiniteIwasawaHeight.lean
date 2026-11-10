module

public import ArtinMatthews.SourceAdelicIwasawaAssembly
public import ArtinMatthews.SourceKubotaBottomRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
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

/-! The finite Iwasawa torus has the usual maximum-norm height. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section
variable (K : Type) [Field K] [NumberField K]

private theorem sourceKPIntegralMatrix_bottom_norm (P : HeightOneSpectrum (𝓞 K))
    (k : GL (Fin 2) (P.adicCompletion K))
    (hk : SourceKPIntegralMatrix (sourceKPFiniteVal K P) k) :
    max ‖k 1 0‖ ‖k 1 1‖ = 1 := by
  have h₀ : ‖k 1 0‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr (hk.entries 1 0)
  have h₁ : ‖k 1 1‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr (hk.entries 1 1)
  rcases sourceKPIntegralMatrix_bottom_unit (sourceKPFiniteVal K P) hk with h | h
  · rw [Valued.toNormedField.norm_eq_one_iff.mpr h, max_eq_left h₁]
  · rw [Valued.toNormedField.norm_eq_one_iff.mpr h, max_eq_right h₀]

theorem sourceKPIwasawa_torus_norm (P : HeightOneSpectrum (𝓞 K))
    (g b : GL (Fin 2) (P.adicCompletion K)) (d : (P.adicCompletion K)ˣ)
    (k : GL (Fin 2) (P.adicCompletion K))
    (hb : b ∈ sourceGL2NormalizedBorel (P.adicCompletion K))
    (hk : SourceKPIntegralMatrix (sourceKPFiniteVal K P) k)
    (he : g = b * GeneralLinearGroup.scalar (Fin 2) d * k) :
    ‖(GeneralLinearGroup.det b : P.adicCompletion K)‖ =
      ‖(GeneralLinearGroup.det g : P.adicCompletion K)‖ / max ‖g 1 0‖ ‖g 1 1‖ ^ 2 := by
  have h₀ : g 1 0 = (d : P.adicCompletion K) * k 1 0 := by
    rw [he, sourceGL2_bottom_left_mul, sourceKPMatrix_right_scalar_entry,
      sourceKPMatrix_right_scalar_entry, hb.1, hb.2]
    ring
  have h₁ : g 1 1 = (d : P.adicCompletion K) * k 1 1 := by
    rw [he, sourceGL2_bottom_right_mul, sourceKPMatrix_right_scalar_entry,
      sourceKPMatrix_right_scalar_entry, hb.1, hb.2]
    ring
  have hmax : max ‖g 1 0‖ ‖g 1 1‖ = ‖(d : P.adicCompletion K)‖ := by
    rw [h₀, h₁, norm_mul, norm_mul, ← mul_max_of_nonneg _ _ (norm_nonneg _),
      sourceKPIntegralMatrix_bottom_norm K P k hk, mul_one]
  have hdet : ‖(GeneralLinearGroup.det g : P.adicCompletion K)‖ =
      ‖(GeneralLinearGroup.det b : P.adicCompletion K)‖ * ‖(d : P.adicCompletion K)‖ ^ 2 := by
    rw [he, map_mul, map_mul, GeneralLinearGroup.det_scalar]
    simp only [Fintype.card_fin, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow,
      Valued.toNormedField.norm_eq_one_iff.mpr hk.det_unit, mul_one]
  rw [hmax, hdet]
  exact (mul_div_cancel_right₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr d.ne_zero))).symm

theorem sourceKPLocalIwasawa_torus_norm (P : HeightOneSpectrum (𝓞 K))
    (g : GL (Fin 2) (P.adicCompletion K)) :
    ‖(GeneralLinearGroup.det (sourceKPLocalIwasawa K P g).borel : P.adicCompletion K)‖ =
      ‖(GeneralLinearGroup.det g : P.adicCompletion K)‖ / max ‖g 1 0‖ ‖g 1 1‖ ^ 2 :=
  sourceKPIwasawa_torus_norm K P g _ _ _ (sourceKPLocalIwasawa K P g).borel_mem
    (sourceKPLocalIwasawa K P g).integral_mem (sourceKPLocalIwasawa K P g).factor

theorem sourceKPAdeleIwasawa_torus_norm (g : GL (Fin 2) 𝔸ᶠ[K])
    (P : HeightOneSpectrum (𝓞 K)) :
    ‖(GeneralLinearGroup.det (sourceKPAdeleMatrixAt K P (sourceKPAdeleIwasawaBorel K g)) :
        P.adicCompletion K)‖ =
      ‖(GeneralLinearGroup.det (sourceKPAdeleMatrixAt K P g) : P.adicCompletion K)‖ /
        max ‖sourceKPAdeleMatrixAt K P g 1 0‖ ‖sourceKPAdeleMatrixAt K P g 1 1‖ ^ 2 := by
  rw [sourceKPAdeleIwasawaBorel_at]
  exact sourceKPLocalIwasawa_torus_norm K P _

theorem sourceKPLocalIwasawa_bigCell_torus_norm (P : HeightOneSpectrum (𝓞 K))
    (x : P.adicCompletion K) :
    ‖(GeneralLinearGroup.det (sourceKPLocalIwasawa K P
      (sourceGL2Weyl * sourceGL2Upper x)).borel : P.adicCompletion K)‖ =
        (max 1 ‖x‖)⁻¹ ^ 2 := by
  rw [sourceKPLocalIwasawa_torus_norm]
  simp [map_mul, sourceGL2Weyl, sourceGL2Upper, GeneralLinearGroup.val_det_apply,
    Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two, one_div, inv_pow]

end
end ArtinMatthews
