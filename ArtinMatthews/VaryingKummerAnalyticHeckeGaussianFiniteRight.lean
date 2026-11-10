module

public import ArtinMatthews.VaryingKummerAnalyticHeckeFiniteEulerContinuation
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveGaussianSignal
public import ArtinMatthews.VaryingKummerAnalyticGaussianFiniteContour
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal Gaussian reciprocal of the old-ideal coprime continuation.
Its right-line integrability and bounds are proved by actual Euler factors. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set
open OAI.SevenEighths.Continuation
open scoped NumberField nonZeroDivisors Classical Topology
noncomputable section

theorem exists_idealCoprimeReciprocal_right_bound
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ U : ℝ, 1 ≤ U →
      ∀ {f : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K f) (hf : f ≠ ⊥)
        (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
        (_hnp : ψ.IsNonprincipal) (M : Ideal (𝓞 K)), M ≠ ⊥ → (Ideal.absNorm M : ℝ) ≤ U →
        ∀ s : ℂ, (5/4 : ℝ) ≤ s.re →
          ‖(ψ.idealCoprimeContinued hf hprim M s)⁻¹‖ ≤ B*U^ε := by
  obtain ⟨D,hD,hdel⟩ := exists_idealEulerDeletion_subpower_bound K ε hε
  refine ⟨primitiveReciprocalBound K*D,mul_pos (primitiveReciprocalBound_pos K) hD,?_⟩
  intro U hU f ψ hf hprim hnp M hM hMU s hs
  have hL := ψ.primitiveReciprocal_norm_le hf hprim hnp hs
  have hd := hdel ψ M hM s (by linarith : (1/2 : ℝ) ≤ s.re)
  have hdinv : ‖(ψ.idealEulerDeletion M s)⁻¹‖ ≤ D*U^ε := by
    have hsmall : ‖(ψ.idealEulerDeletion M s)⁻¹‖ ≤ D*(Ideal.absNorm M : ℝ)^ε := by
      linarith [norm_nonneg (ψ.idealEulerDeletion M s)]
    exact hsmall.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hMU hε.le) hD.le)
  rw [ψ.idealCoprimeContinued_inv_norm]
  change ‖(ψ.primitiveContinued hf hprim s)⁻¹‖ ≤ primitiveReciprocalBound K at hL
  exact (mul_le_mul hL hdinv (norm_nonneg _) (primitiveReciprocalBound_pos K).le).trans_eq (by ring)

namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {f : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K f) (hf : f ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)

def idealCoprimeReciprocal (M : Ideal (𝓞 K)) (s : ℂ) : ℂ :=
  (ψ.idealCoprimeContinued hf hprim M s)⁻¹

def idealCoprimeGaussianIntegrand (M : Ideal (𝓞 K)) (c Z : ℝ) : ℂ → ℂ :=
  gaussianContourIntegrand (ψ.idealCoprimeReciprocal hf hprim M) c Z

def idealCoprimeGaussianSignal (M : Ideal (𝓞 K)) (c Z : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*∫ y : ℝ, ψ.idealCoprimeGaussianIntegrand hf hprim M c Z (2+(y : ℂ)*I)

def idealCoprimeGaussianLeft (M : Ideal (𝓞 K)) (c Z T : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*finiteVerticalIntegral (ψ.idealCoprimeGaussianIntegrand hf hprim M c Z) (499/500) T

def idealCoprimeGaussianHorizontal (M : Ideal (𝓞 K)) (c Z T : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*finiteHorizontalError (ψ.idealCoprimeGaussianIntegrand hf hprim M c Z) (499/500) 2 T

def idealCoprimeGaussianTail (M : Ideal (𝓞 K)) (c Z T : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*rightVerticalTail (ψ.idealCoprimeGaussianIntegrand hf hprim M c Z) 2 T

theorem idealCoprimeGaussianIntegrand_norm (M : Ideal (𝓞 K)) (c x y : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    ‖ψ.idealCoprimeGaussianIntegrand hf hprim M c Z ((x : ℂ)+(y : ℂ)*I)‖ =
      Z^(x+c)*Real.exp ((x-5/6)^2)*‖(ψ.idealCoprimeContinued hf hprim M ((x : ℂ)+(y : ℂ)*I))⁻¹‖*
        Real.exp (-(y^2)) :=
  norm_gaussianContourIntegrand _ _ _ _ hZ

theorem idealCoprimeReciprocal_differentiableAt (hnp : ψ.IsNonprincipal)
    (M : Ideal (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (ψ.idealCoprimeReciprocal hf hprim M) s := by
  apply (ψ.idealCoprimeContinued_entire hf hprim M s).inv
  intro hz
  exact (ψ.primitiveContinued_ne_zero_right hf hprim hnp hs)
    ((ψ.idealCoprimeContinued_zero_iff hf hprim M (by linarith)).mp hz)

theorem idealCoprimeGaussianIntegrand_continuous_right (hnp : ψ.IsNonprincipal)
    (M : Ideal (𝓞 K)) (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    Continuous (fun y : ℝ => ψ.idealCoprimeGaussianIntegrand hf hprim M c Z (2+(y : ℂ)*I)) := by
  have hG : DifferentiableOn ℂ (ψ.idealCoprimeReciprocal hf hprim M) {s : ℂ | 1 < s.re} :=
    fun _ hs => (ψ.idealCoprimeReciprocal_differentiableAt hf hprim hnp M hs).differentiableWithinAt
  have hF := gaussianContourIntegrand_differentiableOn hG c hZ
  apply continuous_iff_continuousAt.mpr
  intro y
  have hz : (2+(y : ℂ)*I) ∈ {s : ℂ | 1 < s.re} := by norm_num
  have hd := hF.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
  exact hd.continuousAt.comp (f := fun y : ℝ => (2 : ℂ)+(y : ℂ)*I) (by fun_prop)

theorem idealCoprimeGaussianIntegrand_integrable_right (hnp : ψ.IsNonprincipal)
    (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    Integrable (fun y : ℝ => ψ.idealCoprimeGaussianIntegrand hf hprim M c Z (2+(y : ℂ)*I)) := by
  obtain ⟨B,_hB,hbound⟩ := exists_idealCoprimeReciprocal_right_bound K 1 (by norm_num)
  have hM1 : 1 ≤ (Ideal.absNorm M : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hM)
  apply integrable_of_gaussian_bound _
    (Z^(2+c)*Real.exp ((2-5/6 : ℝ)^2)*(B*(Ideal.absNorm M : ℝ)))
    (ψ.idealCoprimeGaussianIntegrand_continuous_right hf hprim hnp M c hZ).aestronglyMeasurable
  intro y
  change ‖ψ.idealCoprimeGaussianIntegrand hf hprim M c Z (((2 : ℝ) : ℂ)+(y : ℂ)*I)‖ ≤ _
  rw [ψ.idealCoprimeGaussianIntegrand_norm hf hprim M c 2 y hZ]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa using hbound (Ideal.absNorm M) hM1 ψ hf hprim hnp M hM le_rfl
    (2+(y : ℂ)*I) (by norm_num)

theorem idealCoprimeGaussianSignal_one (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    ψ.idealCoprimeGaussianSignal hf hprim 1 c Z = ψ.primitiveGaussianSignal hf hprim c Z := by
  have hd (s : ℂ) : ψ.idealEulerDeletion 1 s = 1 := by
    have hp : HeckeIdealMobius.primeSupport K (1 : Ideal (𝓞 K)) = ∅ :=
      (HeckeIdealMobius.primeSupport_empty_iff K 1 one_ne_zero).mpr rfl
    simp only [idealEulerDeletion,hp,Finset.prod_empty]
  rw [ψ.primitiveGaussianSignal_eq_contour hf hprim c hZ]
  unfold idealCoprimeGaussianSignal
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [idealCoprimeGaussianIntegrand,gaussianContourIntegrand,idealCoprimeReciprocal,
    idealCoprimeContinued,hd,primitiveReciprocal,mul_one]

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
