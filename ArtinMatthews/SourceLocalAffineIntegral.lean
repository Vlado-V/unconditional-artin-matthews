module

public import ArtinMatthews.SourceJacquetHaar
public import ArtinMatthews.StandardAdelicLocalNontrivial
public import ArtinMatthews.SourceJacquetHaarDilation
public import ArtinMatthews.SourceJacquetIntegrabilityDilation
public import ArtinMatthews.StandardLocalBall
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

/-! Whole-field affine changes of variable for the actual local
additive Haar measure. The finite-place modulus and integrability
are retained explicitly. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical Set
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "μ₀" => sourceJacquetHaar K P

theorem sourceLocalIntegral_translate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u : L) (f : L → V) : (∫ x, f (x + u) ∂μ₀) = ∫ x, f x ∂μ₀ := by
  let : (sourceJacquetHaar K P).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  exact integral_add_right_eq_self f u

theorem sourceLocalIntegrable_translate_iff {V : Type*} [NormedAddCommGroup V]
    (u : L) (f : L → V) : Integrable (fun x => f (x + u)) μ₀ ↔ Integrable f μ₀ := by
  let : (sourceJacquetHaar K P).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  let e := MeasurableEquiv.addRight u
  have he : MeasurePreserving e μ₀ μ₀ := measurePreserving_add_right μ₀ u
  exact he.integrable_comp_emb e.measurableEmbedding

theorem sourceLocalIntegral_mul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hP : P ∉ traceBadPlaces K) (y : Lˣ) (f : L → V) :
    (∫ x, f x ∂μ₀) = ‖(y : L)‖ • ∫ x, f ((y : L) * x) ∂μ₀ := by
  have hs : (fun x : L => (y : L) * x) '' (univ : Set L) = univ :=
    Set.image_univ_of_surjective (mul_left_surjective₀ y.ne_zero)
  have h := sourceJacquetSetIntegral_dilation K P hP y univ f
  simpa only [hs, setIntegral_univ] using h

theorem sourceLocalIntegrable_mul_iff {V : Type*} [NormedAddCommGroup V]
    (hP : P ∉ traceBadPlaces K) (y : Lˣ) (f : L → V) :
    Integrable (fun x => f ((y : L) * x)) μ₀ ↔ Integrable f μ₀ := by
  have hs : (fun x : L => (y : L) * x) '' (univ : Set L) = univ :=
    Set.image_univ_of_surjective (mul_left_surjective₀ y.ne_zero)
  have h := sourceJacquetIntegrableOn_dilation_iff K P hP y univ f
  simpa only [hs, integrableOn_univ] using h.symm

theorem sourceLocalIntegral_div {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hP : P ∉ traceBadPlaces K) (y : Lˣ) (f : L → V) :
    (∫ x, f (x / (y : L)) ∂μ₀) = ‖(y : L)‖ • ∫ x, f x ∂μ₀ := by
  have h := sourceLocalIntegral_mul K P hP y (fun x => f (x / (y : L)))
  have he : (fun x : L => f ((y : L) * x / (y : L))) = f := by
    funext x
    rw [mul_div_cancel_left₀ x y.ne_zero]
  rwa [he] at h

theorem sourceLocalIntegrable_div_iff {V : Type*} [NormedAddCommGroup V]
    (hP : P ∉ traceBadPlaces K) (y : Lˣ) (f : L → V) :
    Integrable (fun x => f (x / (y : L))) μ₀ ↔ Integrable f μ₀ := by
  have he : (fun x : L => f (((y⁻¹ : Lˣ) : L) * x)) = fun x => f (x / (y : L)) := by
    funext x
    rw [Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm]
  rw [← he]
  exact sourceLocalIntegrable_mul_iff K P hP y⁻¹ f

theorem sourceLocalIntegral_affine {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hP : P ∉ traceBadPlaces K) (u : L) (y : Lˣ) (f : L → V) :
    (∫ x, f ((x + u) / (y : L)) ∂μ₀) = ‖(y : L)‖ • ∫ x, f x ∂μ₀ := by
  rw [sourceLocalIntegral_translate K P u (fun x => f (x / (y : L))),
    sourceLocalIntegral_div K P hP y f]

theorem sourceLocalIntegrable_affine_iff {V : Type*} [NormedAddCommGroup V]
    (hP : P ∉ traceBadPlaces K) (u : L) (y : Lˣ) (f : L → V) :
    Integrable (fun x => f ((x + u) / (y : L))) μ₀ ↔ Integrable f μ₀ := by
  rw [sourceLocalIntegrable_translate_iff K P u (fun x => f (x / (y : L))),
    sourceLocalIntegrable_div_iff K P hP y f]

end
end ArtinMatthews
