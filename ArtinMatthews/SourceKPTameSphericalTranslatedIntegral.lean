module

public import ArtinMatthews.SourceKPTameSphericalTranslate
public import ArtinMatthews.SourceKPTameWeylBasisFlip
public import ArtinMatthews.SourceKPTameSphericalIntertwiner
public import ArtinMatthews.SourceKPProjectiveCanonicalFactors
public import ArtinMatthews.SourceKPTameParametricAction
public import ArtinMatthews.SourceKPTameParametricOpenCell
public import ArtinMatthews.SourceLocalAffineIntegral
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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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

/-! The actual standard intertwining integral at every group input.
Absolute integrability follows from the checked identity integral and
the genuine affine Haar change of variables. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "κ₀" => sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆
local notation "z₀" => sourceFiniteKP2ProjectiveCenter K hζ P.val
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "n₀" => fun x : L => l₀ (sourceGL2Upper x)
local notation "a₀" => fun y : Lˣ => l₀ (sourceGL2Diagonal y)
local notation "τ₀" => sourceKPTameParametricBorelRepresentation K hζ P.val h₆ π₀ hπ₀
local notation "F₀" => sourceKPTameSphericalPlainIntegrand K hζ S₀ P
local notation "μ₀" => sourceJacquetHaar K P.val

theorem sourceKPTameSphericalPlainIntegrand_one_integrable
    (hP : P.val ∉ traceBadPlaces K) {s : ℂ} (hs : 0 < s.re) :
    Integrable (F₀ s 1) μ₀ := by
  change Integrable (fun x : L =>
    (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s).val
      ((l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) * 1)) μ₀
  simpa only [mul_one] using
    sourceKPTameSphericalIntertwiner_integrable K hζ S₀ P hP hs

theorem sourceKPTameSphericalPlainIntegrand_integrable
    (hP : P.val ∉ traceBadPlaces K) {s : ℂ} (hs : 0 < s.re) (g : G₀) :
    Integrable (F₀ s g) μ₀ := by
  obtain ⟨z, u, y, k, hg⟩ := sourceFiniteKP2Projective_Iwasawa_canonical K hζ P.val h₆ g
  let A : (ZMod 3 → ℂ) →L[ℂ] (ZMod 3 → ℂ) :=
    LinearMap.toContinuousLinearMap (τ₀ s (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val y⁻¹))
  have hi := (sourceLocalIntegrable_affine_iff K P.val hP u y (F₀ s 1)).mpr
    (sourceKPTameSphericalPlainIntegrand_one_integrable K hζ S₀ P hP hs)
  have he : F₀ s g = fun x => (sourceKPCentralComplex K hζ P.val z : ℂ) •
      A (F₀ s 1 ((x + u) / (y : L))) :=
    funext (sourceKPTameSphericalPlainIntegrand_iwasawa K hζ S₀ P s g z u y k hg)
  rw [he]
  exact (A.integrable_comp hi).smul (sourceKPCentralComplex K hζ P.val z : ℂ)

theorem sourceKPTameSphericalPlainIntegral_iwasawa
    (hP : P.val ∉ traceBadPlaces K) {s : ℂ} (hs : 0 < s.re) (g : G₀)
    (z : rootsOfUnity 3 L) (u : L) (y : Lˣ) (k : SourceFiniteKP2Integral K P.val)
    (hg : g = z₀ z * n₀ u * a₀ y * κ₀ k) :
    (∫ x, F₀ s g x ∂μ₀) = (sourceKPCentralComplex K hζ P.val z : ℂ) •
      τ₀ s (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val y⁻¹)
        (‖(y : L)‖ • sourceKPTameSphericalIntertwiner K hζ S₀ P s) := by
  let A : (ZMod 3 → ℂ) →L[ℂ] (ZMod 3 → ℂ) :=
    LinearMap.toContinuousLinearMap (τ₀ s (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val y⁻¹))
  have hi := (sourceLocalIntegrable_affine_iff K P.val hP u y (F₀ s 1)).mpr
    (sourceKPTameSphericalPlainIntegrand_one_integrable K hζ S₀ P hP hs)
  have he : F₀ s g = fun x => (sourceKPCentralComplex K hζ P.val z : ℂ) •
      A (F₀ s 1 ((x + u) / (y : L))) :=
    funext (sourceKPTameSphericalPlainIntegrand_iwasawa K hζ S₀ P s g z u y k hg)
  rw [he, integral_smul, A.integral_comp_comm hi, sourceLocalIntegral_affine K P.val hP u y]
  simp only [sourceKPTameSphericalPlainIntegrand, mul_one, sourceKPTameSphericalIntertwiner]
  rfl

theorem sourceKPTameSphericalTranslatedIntertwiner
    (hP : P.val ∉ traceBadPlaces K) {s : ℂ} (hs : 0 < s.re) (g : G₀) :
    sourceKPTameWeylBasisFlip (∫ x, F₀ s g x ∂μ₀) =
      sourceKPUnramifiedScatteringFactor P.val s •
        (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ (-s)).val g := by
  obtain ⟨z, u, y, k, hg⟩ := sourceFiniteKP2Projective_Iwasawa_canonical K hζ P.val h₆ g
  rw [sourceKPTameSphericalPlainIntegral_iwasawa K hζ S₀ P hP hs g z u y k hg,
    sourceKPTameSphericalIntertwiner_eq K hζ S₀ P hP hs]
  have hsection :
      (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ (-s)).val g =
        (sourceKPCentralComplex K hζ P.val z : ℂ) •
          τ₀ (-s) (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val y) (sourceJacquetBasis 0) := by
    rw [hg, sourceKPTameParametricSpherical_eval_right,
      mul_assoc (z₀ z) (n₀ u) (a₀ y), sourceKPTameParametricSpherical_center]
    congr 1
    change (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ (-s)).val
      (l₀ (sourceGL2Upper u) * l₀ (sourceGL2Diagonal y)) = _
    rw [← sourceFiniteKPProjectiveBorelUpper_val,
      sourceKPTameParametricSpherical_covariant, sourceKPTameParametricBorel_upper]
    have hv := sourceKPTameParametricSpherical_covariant K hζ S₀ P (-s)
      (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val y) 1
    rw [mul_one, sourceKPTameParametricSphericalSection_one] at hv
    exact hv
  rw [hsection]
  have hreal (r : ℝ) (v : ZMod 3 → ℂ) : r • v = (r : ℂ) • v := by
    ext i
    rfl
  calc
    _ = sourceKPUnramifiedScatteringFactor P.val s •
        (sourceKPCentralComplex K hζ P.val z : ℂ) •
          sourceKPTameWeylBasisFlip (‖(y : L)‖ •
            τ₀ s (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val y⁻¹) (sourceJacquetBasis 0)) := by
      simp only [hreal, map_smul, smul_smul]
      congr 1
      ring
    _ = _ := by rw [sourceKPTameWeylBasisFlip_diagonal K hζ S₀ P s y]

end
end ArtinMatthews
