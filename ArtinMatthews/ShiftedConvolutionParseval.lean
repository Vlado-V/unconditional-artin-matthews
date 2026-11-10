module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Finite Fourier-polynomial Parseval estimates used for the literal
convolution coefficients in (5.6). Haar measure is normalized to total mass one. -/

noncomputable section
open Complex MeasureTheory AddCircle Finset
open scoped BigOperators

namespace ArtinMatthews

/-- A finite trigonometric polynomial with explicitly supplied integer frequencies. -/
def shiftedTrigPolynomial {ι : Type*} (S : Finset ι) (a : ι → ℂ) (f : ι → ℤ) :
    C(AddCircle (1 : ℝ), ℂ) := ∑ i ∈ S, a i • fourier (f i)

@[simp] theorem shiftedTrigPolynomial_apply {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (f : ι → ℤ) (x : AddCircle (1 : ℝ)) :
    shiftedTrigPolynomial S a f x = ∑ i ∈ S, a i * fourier (f i) x := by
  simp [shiftedTrigPolynomial]

/-- Exact coefficients, including collisions among frequencies. -/
theorem fourierCoeff_shiftedTrigPolynomial {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (f : ι → ℤ) (r : ℤ) :
    fourierCoeff (shiftedTrigPolynomial S a f) r =
      ∑ i ∈ S, if f i = r then a i else 0 := by
  classical
  have hfun : (shiftedTrigPolynomial S a f : AddCircle (1 : ℝ) → ℂ) =
      ∑ i ∈ S, fun x ↦ a i * fourier (f i) x := by
    ext x
    simp
  rw [hfun, fourierCoeff.sum]
  · simp only [Finset.sum_apply, fourierCoeff.const_mul, fourierCoeff_fourier,
      Pi.single_apply]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp_all
  · intro i _
    exact ((fourier (f i)).continuous.const_mul (a i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Parseval for a continuous polynomial, via the actual Hilbert-basis theorem. -/
theorem shiftedPolynomial_parseval (P : C(AddCircle (1 : ℝ), ℂ)) :
    HasSum (fun r : ℤ ↦ ‖fourierCoeff P r‖ ^ 2)
      (∫ x : AddCircle (1 : ℝ), ‖P x‖ ^ 2 ∂haarAddCircle) := by
  have hp := hasSum_sq_fourierCoeff (P.toLp 2 haarAddCircle ℂ)
  simp only [fourierCoeff_toLp] at hp
  convert hp using 1
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toAEEqFun haarAddCircle P] with x hx
  exact congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx.symm

/-- With distinct frequencies, Parseval is exactly the sum of coefficient squares. -/
theorem shiftedTrigPolynomial_integral_sq {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (f : ι → ℤ) (hf : Set.InjOn f S) :
    (∫ x : AddCircle (1 : ℝ), ‖shiftedTrigPolynomial S a f x‖ ^ 2 ∂haarAddCircle) =
      ∑ i ∈ S, ‖a i‖ ^ 2 := by
  classical
  rw [← (shiftedPolynomial_parseval _).tsum_eq]
  rw [tsum_eq_sum (s := S.image f)]
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [fourierCoeff_shiftedTrigPolynomial]
      have he : (∑ j ∈ S, if f j = f i then a j else 0) = a i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j hj hji
          have hne : f j ≠ f i := fun h ↦ hji (hf hj hi h)
          simp [hne]
        · exact fun h ↦ (h hi).elim
      rw [he]
    · exact hf
  · intro r hr
    rw [fourierCoeff_shiftedTrigPolynomial]
    have hz : (∑ i ∈ S, if f i = r then a i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hne : f i ≠ r := fun h ↦ hr (Finset.mem_image.mpr ⟨i, hi, h⟩)
      simp [hne]
    simp [hz]

/-- A bounded first factor controls any finite portion of the coefficient
energy of its product, with no frequency-spacing loss. -/
theorem shiftedPolynomial_product_energy_le {ι : Type*} (S : Finset ι)
    (b : ι → ℂ) (g : ι → ℤ) (hg : Set.InjOn g S)
    (P : C(AddCircle (1 : ℝ), ℂ)) (C : ℝ) (_hC : 0 ≤ C)
    (hP : ∀ x, ‖P x‖ ≤ C) (R : Finset ℤ) :
    ∑ r ∈ R, ‖fourierCoeff (P * shiftedTrigPolynomial S b g) r‖ ^ 2 ≤
      C ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2 := by
  let Q := shiftedTrigPolynomial S b g
  have hp := shiftedPolynomial_parseval (P * Q)
  calc
    _ ≤ ∫ x : AddCircle (1 : ℝ), ‖(P * Q) x‖ ^ 2 ∂haarAddCircle :=
      sum_le_hasSum R (fun r _ ↦ sq_nonneg _) hp
    _ ≤ ∫ x : AddCircle (1 : ℝ), C ^ 2 * ‖Q x‖ ^ 2 ∂haarAddCircle := by
      apply integral_mono
      · exact ((P * Q).continuous.norm.pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact ((Q.continuous.norm.pow 2).const_mul _).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · intro x
        simp only [ContinuousMap.mul_apply, norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hP x) 2)
          (sq_nonneg _)
    _ = _ := by rw [integral_const_mul, shiftedTrigPolynomial_integral_sq S b g hg]

/-- Multiplication of two finite Fourier polynomials convolves their exact integer frequencies. -/
theorem fourierCoeff_shiftedTrigProduct {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (f : ι → ℤ) (g : κ → ℤ) (r : ℤ) :
    fourierCoeff (shiftedTrigPolynomial S a f * shiftedTrigPolynomial T b g) r =
      ∑ i ∈ S, ∑ j ∈ T, if f i + g j = r then a i * b j else 0 := by
  have he : shiftedTrigPolynomial S a f * shiftedTrigPolynomial T b g =
      shiftedTrigPolynomial (S ×ˢ T) (fun p ↦ a p.1 * b p.2)
        (fun p ↦ f p.1 + g p.2) := by
    ext x
    simp only [ContinuousMap.mul_apply, shiftedTrigPolynomial_apply,
      Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [fourier_add]
    ring
  rw [he, fourierCoeff_shiftedTrigPolynomial, Finset.sum_product]

end ArtinMatthews
