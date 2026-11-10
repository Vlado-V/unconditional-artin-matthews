module

public import ArtinMatthews.VaryingKummerAnalyticHeckeGaussianFiniteRight
public import ArtinMatthews.VaryingKummerAnalyticGaussianFiniteBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The finite-height left shift for the actual complementary primitive
family, including an arbitrary old ideal modulus of norm at most U.
The horizontal and right-tail errors remain explicit. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set
open OAI.SevenEighths.Continuation OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical Topology BigOperators
noncomputable section

theorem exists_actual_good_family_gaussian_finite_shift
    (K : Type*) [Field K] [NumberField K] :
    ∃ r C₀ U₀ : ℝ, 0 < r ∧ r < 1/10 ∧ 0 < C₀ ∧ 2 ≤ U₀ ∧
      (∀ U : ℝ, U₀ ≤ U →
        ∀ (T : Finset (IdealConductorModulus K))
          (A : ∀ f : IdealConductorModulus K, Finset (EvenIdealRayCharacter K f.val)),
          (∀ f ∈ T, (Ideal.absNorm f.val : ℝ) ≤ U) →
          (∀ f ∈ T, ∀ ψ ∈ A f, IsPrimitiveOnIdeals ψ.residue) →
          (∀ f ∈ T, ∀ ψ ∈ A f, ψ.IsNonprincipal) →
          (∑ f ∈ T, ((primitiveExceptionalCoefficients K f (A f) U r).card : ℝ)) ≤ C₀*U^(1/2 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
        ∀ U : ℝ, U₀ ≤ U →
        ∀ (T : Finset (IdealConductorModulus K))
          (A : ∀ f : IdealConductorModulus K, Finset (EvenIdealRayCharacter K f.val)),
          (∀ f ∈ T, (Ideal.absNorm f.val : ℝ) ≤ U) →
          (∀ f ∈ T, ∀ ψ ∈ A f, IsPrimitiveOnIdeals ψ.residue) →
          (∀ f ∈ T, ∀ ψ ∈ A f, ψ.IsNonprincipal) →
          ∀ f ∈ T, ∀ ψ ∈ A f, ∀ hprim : IsPrimitiveOnIdeals ψ.residue,
            ψ.coefficient ∉ primitiveExceptionalCoefficients K f (A f) U r →
            ∀ M : Ideal (𝓞 K), M ≠ ⊥ → (Ideal.absNorm M : ℝ) ≤ U →
            ∀ c Z : ℝ, 1 ≤ Z →
              ψ.idealCoprimeGaussianSignal f.property hprim M c Z =
                ψ.idealCoprimeGaussianLeft f.property hprim M c Z (U^r)+
                  ψ.idealCoprimeGaussianHorizontal f.property hprim M c Z (U^r)+
                  ψ.idealCoprimeGaussianTail f.property hprim M c Z (U^r) ∧
              ‖ψ.idealCoprimeGaussianLeft f.property hprim M c Z (U^r)‖ ≤
                C*U^ε*Z^((499/500 : ℝ)+c) ∧
              ‖ψ.idealCoprimeGaussianHorizontal f.property hprim M c Z (U^r)‖ ≤
                C*U^ε*Z^(2+c)*Real.exp (-((U^r)^2)) ∧
              ‖ψ.idealCoprimeGaussianTail f.property hprim M c Z (U^r)‖ ≤
                C*U^ε*Z^(2+c)*Real.exp (-((U^r)^2)/2)) := by
  obtain ⟨r,C₀,U₀,hr,hr',hC₀,hU₀,hcount,hgood⟩ := exists_actual_primitive_good_family_with_deletions K
  refine ⟨r,C₀,U₀,hr,hr',hC₀,hU₀,hcount,?_⟩
  intro ε hε
  obtain ⟨B,hB,hbox⟩ := hgood ε hε
  obtain ⟨D,hD,hright⟩ := exists_idealCoprimeReciprocal_right_bound K ε hε
  let q : ℂ := 1/(2*Real.pi)
  let E₁ : ℝ := Real.exp (((499/500 : ℝ)-5/6)^2)
  let E₂ : ℝ := Real.exp (((2 : ℝ)-5/6)^2)
  let C₁ : ℝ := ‖q‖*B*E₁*gaussianLineMass
  let C₂ : ℝ := ‖q‖*2*B*((2 : ℝ)-499/500)*E₂
  let C₃ : ℝ := ‖q‖*D*E₂*gaussianHalfLineMass
  let C : ℝ := C₁+C₂+C₃+1
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; exact mul_nonneg (by positivity) gaussianLineMass_nonneg
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂,E₂]; positivity
  have hC₃ : 0 ≤ C₃ := by dsimp [C₃]; exact mul_nonneg (by positivity) gaussianHalfLineMass_nonneg
  have hC : 0 < C := by dsimp [C]; linarith
  have h1C : C₁ ≤ C := by dsimp [C]; linarith
  have h2C : C₂ ≤ C := by dsimp [C]; linarith
  have h3C : C₃ ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro U hU T A hT hA hnp f hfT ψ hψ hprim hcomp M hM hMU c Z hZ
  have hU1 : 1 ≤ U := by linarith [hU₀.trans hU]
  have hUpos : 0 < U := zero_lt_one.trans_le hU1
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hHpos : 0 < U^r := Real.rpow_pos_of_pos hUpos r
  have hnp' := hnp f hfT ψ hψ
  let F := ψ.idealCoprimeGaussianIntegrand f.property hprim M c Z
  have hG (x : ℝ) (hx : x ∈ Icc (499/500 : ℝ) 2) (y : ℝ) (hy : |y| ≤ U^r) :
      ‖(ψ.idealCoprimeContinued f.property hprim M ((x : ℂ)+(y : ℂ)*I))⁻¹‖ ≤ B*U^ε := by
    apply hbox U hU T A hT hA hnp f hfT ψ hψ hprim hcomp M hM hMU
    · simpa using hx.1
    · simpa using hy.trans (show U^r ≤ 2*U^r by linarith)
  have hR (y : ℝ) :
      ‖(ψ.idealCoprimeContinued f.property hprim M (((2 : ℝ) : ℂ)+(y : ℂ)*I))⁻¹‖ ≤ D*U^ε :=
    hright U hU1 ψ f.property hprim hnp' M hM hMU _ (by norm_num)
  have hF : DifferentiableOn ℂ F {z : ℂ | (499/500 : ℝ) ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ U^r} := by
    apply gaussianContourIntegrand_differentiableOn _ c hZpos
    intro z hz
    apply ((ψ.idealCoprimeContinued_entire f.property hprim M z).inv ?_).differentiableWithinAt
    intro hzero
    apply primitiveExceptionalCoefficients_complement_nonvanishing K f (A f) U r ψ hψ hprim hcomp z
      (by linarith [hz.1]) (hz.2.2.trans (by linarith))
    exact (ψ.idealCoprimeContinued_zero_iff f.property hprim M (by linarith [hz.1])).mp hzero
  have hi : Integrable (fun y : ℝ => F (2+(y : ℂ)*I)) :=
    ψ.idealCoprimeGaussianIntegrand_integrable_right f.property hprim hnp' M hM c hZpos
  have hFeq (x y : ℝ) : ‖F ((x : ℂ)+(y : ℂ)*I)‖ =
      Z^(x+c)*Real.exp ((x-5/6)^2)*
        ‖(ψ.idealCoprimeContinued f.property hprim M ((x : ℂ)+(y : ℂ)*I))⁻¹‖*Real.exp (-(y^2)) :=
    ψ.idealCoprimeGaussianIntegrand_norm f.property hprim M c x y hZpos
  have hleft (y : ℝ) (hy : |y| ≤ U^r) :
      ‖F (((499/500 : ℝ) : ℂ)+(y : ℂ)*I)‖ ≤
        (B*U^ε*Z^((499/500 : ℝ)+c)*E₁)*Real.exp (-(y^2)) := by
    rw [hFeq]
    have H := hG (499/500) (by constructor <;> norm_num) y hy
    calc
      _ ≤ Z^((499/500 : ℝ)+c)*Real.exp (((499/500 : ℝ)-5/6)^2)*(B*U^ε)*Real.exp (-(y^2)) := by gcongr
      _ = _ := by dsimp [E₁]; ring
  have hstrip (x : ℝ) (hx : x ∈ Icc (499/500 : ℝ) 2) (y : ℝ) (hy : |y| ≤ U^r) :
      ‖F ((x : ℂ)+(y : ℂ)*I)‖ ≤ (B*U^ε*Z^(2+c)*E₂)*Real.exp (-(y^2)) := by
    rw [hFeq]
    have hpow : Z^(x+c) ≤ Z^(2+c) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith [hx.2])
    have hexp : Real.exp ((x-5/6)^2) ≤ E₂ := by
      apply Real.exp_le_exp.mpr
      have hxlo := hx.1
      have hxhi := hx.2
      nlinarith
    have hGG := hG x hx y hy
    calc
      _ ≤ Z^(2+c)*E₂*(B*U^ε)*Real.exp (-(y^2)) := by gcongr
      _ = _ := by ring
  have hrightF (y : ℝ) : ‖F (2+(y : ℂ)*I)‖ ≤
      (D*U^ε*Z^(2+c)*E₂)*Real.exp (-(y^2)) := by
    change ‖F (((2 : ℝ) : ℂ)+(y : ℂ)*I)‖ ≤ _
    rw [hFeq]
    have H := hR y
    calc
      _ ≤ Z^(2+c)*Real.exp (((2 : ℝ)-5/6)^2)*(D*U^ε)*Real.exp (-(y^2)) := by gcongr
      _ = _ := by dsimp [E₂]; ring
  have hEq := full_vertical_finite_shift F (by norm_num : (499/500 : ℝ) ≤ 2) hHpos.le hF hi
  have hL := finiteVerticalIntegral_norm_le F hHpos.le (by dsimp [E₁]; positivity) hleft
  have hH := finiteHorizontalError_norm_le F (by norm_num : (499/500 : ℝ) ≤ 2) hHpos.le hstrip
  have hTail := rightVerticalTail_norm_le F hHpos.le (by dsimp [E₂]; positivity) hrightF
  refine ⟨?_,?_,?_,?_⟩
  · change q*(∫ y : ℝ, F (((2 : ℝ) : ℂ)+(y : ℂ)*I)) =
      q*finiteVerticalIntegral F (499/500) (U^r)+q*finiteHorizontalError F (499/500) 2 (U^r)+
        q*rightVerticalTail F 2 (U^r)
    rw [hEq]
    ring
  · change ‖q*finiteVerticalIntegral F (499/500) (U^r)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ ‖q‖*((B*U^ε*Z^((499/500 : ℝ)+c)*E₁)*gaussianLineMass) :=
        mul_le_mul_of_nonneg_left hL (norm_nonneg _)
      _ = C₁*(U^ε*Z^((499/500 : ℝ)+c)) := by dsimp [C₁]; ring
      _ ≤ C*(U^ε*Z^((499/500 : ℝ)+c)) := mul_le_mul_of_nonneg_right h1C (by positivity)
      _ = _ := by ring
  · change ‖q*finiteHorizontalError F (499/500) 2 (U^r)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ ‖q‖*(2*(B*U^ε*Z^(2+c)*E₂)*((2 : ℝ)-499/500)*Real.exp (-((U^r)^2))) :=
        mul_le_mul_of_nonneg_left hH (norm_nonneg _)
      _ = C₂*(U^ε*Z^(2+c)*Real.exp (-((U^r)^2))) := by dsimp [C₂]; ring
      _ ≤ C*(U^ε*Z^(2+c)*Real.exp (-((U^r)^2))) := mul_le_mul_of_nonneg_right h2C (by positivity)
      _ = _ := by ring
  · change ‖q*rightVerticalTail F 2 (U^r)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ ‖q‖*((D*U^ε*Z^(2+c)*E₂)*gaussianHalfLineMass*Real.exp (-((U^r)^2)/2)) :=
        mul_le_mul_of_nonneg_left hTail (norm_nonneg _)
      _ = C₃*(U^ε*Z^(2+c)*Real.exp (-((U^r)^2)/2)) := by dsimp [C₃]; ring
      _ ≤ C*(U^ε*Z^(2+c)*Real.exp (-((U^r)^2)/2)) := mul_le_mul_of_nonneg_right h3C (by positivity)
      _ = _ := by ring

end
end ArtinMatthews.VaryingKummerAnalytic
