module

public import ArtinMatthews.SourceReflectionNumeratorReindex
public import ArtinMatthews.SourceReflectionRotatedMass
public import ArtinMatthews.SourceSLocalTensorOrbitReflection
public import ArtinMatthews.SourceThetaWeightedSheet
public import ArtinMatthews.SourceReflectionFiniteGaussian
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

/-! A common positive scalar in the reflected coefficient majorant can
be carried through the native quotient orbit and Gaussian profile. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory SourceReflection SourcePhysical
open scoped NumberField Classical BigOperators ENNReal
noncomputable section

namespace SourcePhysical

theorem sourceSLocalTensorOrbit_const_mul {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (c : ℂ) (G : SWholeUnits F S → ℂ)
    (u : SWholeUnits F S) (q : SNormOneSixthQuotient F S) :
    sourceSLocalTensorOrbit S (fun z => c * G z) u q =
      c * sourceSLocalTensorOrbit S G u q := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  change sourceSLocalTensorOrbit S (fun z => c * G z) u (sNormOneSixthQuotientMap F S y) =
    c * sourceSLocalTensorOrbit S G u (sNormOneSixthQuotientMap F S y)
  simp only [sourceSLocalTensorOrbit_mk, tsum_mul_left]

end SourcePhysical

namespace SourceReflection

theorem sourceThetaGaussianProfile_const_mul (C₀ A₀ : ℝ) (r : ℕ) (τ : ℝ)
    (c : ℂ) (H : ℝ → ℂ) (R : ℝ) :
    sourceThetaGaussianProfile C₀ A₀ r τ (fun T => c * H T) R =
      c * sourceThetaGaussianProfile C₀ A₀ r τ H R := by
  calc
    _ = mellin (fun T : ℝ => c • (sourceThetaGaussianKernel C₀ A₀ r T * H (R * T ^ τ))) 0 := by
      unfold sourceThetaGaussianProfile
      apply congrArg (fun G : ℝ → ℂ => mellin G 0)
      funext T
      exact mul_left_comm _ _ _
    _ = _ := mellin_const_smul _ _ _

end SourceReflection

namespace SourceEulerAssembly

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (v : InfinitePlace F) {δ : ℝ}
variable {V X : Type*} [Fintype V] [Fintype X]
variable (D : V → SourceThetaRotatedTensor F (sourceHilbertSet F S₀) hζ v δ)
variable (f : Finset (SourceExteriorPrime F S₀))
variable (d : SourcePrimeExponents F S₀)

local notation "S" => sourceHilbertSet F S₀
local notation "U" => SWholeUnits F S
local notation "Y" => SNormOne F S
local notation "ν" => sourceSLocalNormalizedSheetMeasure F hζ S v
local notation "μ" => sNormOneQuotientMeasure F S ν
local notation "Idx" => SourceReflectionTermIndex F S₀ f
local notation "I" => SourceReflectionSupportedTermIndex F S₀ f d × X

private def scaledTermLength (i : Idx) : ℝ :=
  sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val

local notation "L" => scaledTermLength F S₀ f

private theorem norm_div_real_le {M b : ℝ} (hM : 0 < M) {z : ℂ}
    (hz : ‖z‖ ≤ M * b) : ‖z / (M : ℂ)‖ ≤ b := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, div_le_iff₀ hM, mul_comm b M]
  exact hz

private theorem real_mul_div_cancel {M : ℝ} (hM : M ≠ 0) (z : ℂ) :
    (M : ℂ) * (z / (M : ℂ)) = z := by
  rw [mul_comm, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hM)]

private theorem rotatedTerm_rescale (j : Idx → V) (a : Idx → ℂ) (w : Idx → U → ℂ)
    {M : ℝ} (hM : M ≠ 0) (i : Idx) :
    sourceReflectionRotatedTerm F S₀ hζ v D f j a w i =
      fun z => (M : ℂ) * sourceReflectionRotatedTerm F S₀ hζ v D f j
        (fun i => a i / (M : ℂ)) w i z := by
  funext z
  unfold sourceReflectionRotatedTerm
  rw [← mul_assoc (M : ℂ) (a i / (M : ℂ)), real_mul_div_cancel hM]

theorem sourceReflectionRotatedOrbit_supportedFiniteMass_scaled
    (hδ : 0 ≤ δ) {σ : ℝ} (hσ : 1/2 < σ)
    (j : X → Idx → V) (a : X → Idx → ℂ) {M : ℝ} (hM : 0 < M)
    (ha : ∀ x i, ‖a x i‖ ≤ M * sourceReflectionDirichletTerm F S₀ f 0 i)
    (w : X → Idx → U → ℂ) (hw : ∀ x i z, ‖w x i z‖ ≤ 1)
    (u : X → ℝ → Idx → U)
    (hu : ∀ x T, 0 < T → ∀ i, sLocalNorm F S (u x T i) = L i * T)
    (T : ℝ) (hT : 0 < T) :
    (∑' i : I, ∫⁻ y : Y, ‖sourceReflectionRotatedTerm F S₀ hζ v D f
      (j i.2) (a i.2) (w i.2) i.1.val ((y : U) * u i.2 T i.1.val)‖ₑ ∂ν) < ⊤ := by
  let a₀ (x : X) (i : Idx) := a x i / (M : ℂ)
  let term (i : I) := sourceReflectionRotatedTerm F S₀ hζ v D f (j i.2) (a₀ i.2) (w i.2) i.1.val
  have hmass := sourceReflectionRotatedOrbit_supportedFiniteMass F S₀ hζ v D f d
    hδ hσ j a₀ (fun x i => norm_div_real_le hM (ha x i)) w hw u hu T hT
  calc
    _ = ‖(M : ℂ)‖ₑ * ∑' i : I, ∫⁻ y : Y, ‖term i ((y : U) * u i.2 T i.1.val)‖ₑ ∂ν := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro i
      rw [rotatedTerm_rescale F S₀ hζ v D f (j i.2) (a i.2) (w i.2) hM.ne' i.1.val]
      simp only [enorm_mul]
      exact lintegral_const_mul' _ _ enorm_ne_top
    _ < ⊤ := ENNReal.mul_lt_top enorm_lt_top hmass

theorem sourceReflectionRotatedOrbit_supportedFiniteGaussian_scaled
    (C₀ A₀ : ℝ) (r : ℕ) (hδ : 0 ≤ δ) {σ : ℝ} (hσ : 1/2 < σ)
    (j : X → Idx → V) (a : X → Idx → ℂ) {M : ℝ} (hM : 0 < M)
    (ha : ∀ x i, ‖a x i‖ ≤ M * sourceReflectionDirichletTerm F S₀ f 0 i)
    (w : X → Idx → U → ℂ) (hwm : ∀ x i, Measurable (w x i))
    (hw : ∀ x i z, ‖w x i z‖ ≤ 1)
    (u : X → ℝ → Idx → U) (hu : ∀ x T, 0 < T → ∀ i, sLocalNorm F S (u x T i) = L i * T)
    {R : ℝ} (hR : 0 < R) :
    sourceThetaGaussianProfile C₀ A₀ r (-1)
      (fun T => ∫ q, ∑' i : I, sourceSLocalTensorOrbit S
        (sourceReflectionRotatedTerm F S₀ hζ v D f (j i.2) (a i.2) (w i.2) i.1.val)
        (u i.2 T i.1.val) q ∂μ) R =
      ∑' i : I, a i.2 i.1.val * sourceThetaGaussianProfile C₀ A₀ r (-1)
        ((D (j i.2 i.1.val)).weightedSheet 0 (w i.2 i.1.val)) (L i.1.val * R) := by
  let a₀ (x : X) (i : Idx) := a x i / (M : ℂ)
  let P (b : X → Idx → ℂ) (T : ℝ) := ∫ q, ∑' i : I, sourceSLocalTensorOrbit S
    (sourceReflectionRotatedTerm F S₀ hζ v D f (j i.2) (b i.2) (w i.2) i.1.val)
    (u i.2 T i.1.val) q ∂μ
  have hP : P a = fun T => (M : ℂ) * P a₀ T := by
    funext T
    dsimp only [P]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with q
    rw [← tsum_mul_left]
    apply tsum_congr
    intro i
    rw [rotatedTerm_rescale F S₀ hζ v D f (j i.2) (a i.2) (w i.2) hM.ne' i.1.val,
      sourceSLocalTensorOrbit_const_mul]
  have h := sourceReflectionRotatedOrbit_supportedFiniteGaussian F S₀ hζ v D f d
    C₀ A₀ r hδ hσ j a₀ (fun x i => norm_div_real_le hM (ha x i)) w hwm hw u hu hR
  change sourceThetaGaussianProfile C₀ A₀ r (-1) (P a₀) R = _ at h
  change sourceThetaGaussianProfile C₀ A₀ r (-1) (P a) R = _
  rw [hP, sourceThetaGaussianProfile_const_mul, h, ← tsum_mul_left]
  apply tsum_congr
  intro i
  rw [← mul_assoc]
  exact congrArg (· * _) (real_mul_div_cancel hM.ne' (a i.2 i.1.val))

end SourceEulerAssembly
end
end ArtinMatthews
