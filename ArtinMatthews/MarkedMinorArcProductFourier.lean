module

public import ArtinMatthews.MarkedMinorArcOperator
public import Mathlib.Analysis.Fourier.AddCircle


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite product-variable Fourier transport. The integer product
supports are arbitrary finite sets; no equidistribution premise occurs. -/
namespace ArtinMatthews
open Matrix MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The literal Fourier polynomial of coefficients on a finite integer support. -/
noncomputable def markedProductFourierPolynomial (S : Finset ℤ) (c : S → ℂ) :
    C(AddCircle (1 : ℝ), ℂ) :=
  ∑ a : S, c a • fourier a.1

/-- Exact Parseval for arbitrary finite product supports, with normalized
circle Haar measure. -/
theorem markedProductFourierPolynomial_parseval (S : Finset ℤ) (c : S → ℂ) :
    (∫ θ : AddCircle (1 : ℝ), ‖markedProductFourierPolynomial S c θ‖^2
      ∂AddCircle.haarAddCircle) = ∑ a : S, ‖c a‖^2 := by
  classical
  let p := markedProductFourierPolynomial S c
  have hp : ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ p =
      ∑ a : S, c a • fourierLp (T := (1:ℝ)) 2 a.1 := by
    simp only [p,markedProductFourierPolynomial,map_sum,map_smul,fourierLp]
  have ho := orthonormal_fourier (T := (1:ℝ))
  have hs := (ho.comp (fun a : S => a.1) Subtype.val_injective).inner_sum c c Finset.univ
  simp only [Function.comp_apply] at hs
  rw [← hp,ContinuousMap.inner_toLp] at hs
  have hreal := congrArg (RCLike.re : ℂ → ℝ) hs
  rw [← integral_re] at hreal
  · simpa [Complex.mul_conj,Complex.conj_mul',Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_pow] using hreal
  · exact p.continuous.mul p.continuous.star |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The squared scalar L² norm is the actual normalized Haar integral. -/
theorem markedProductL2_norm_sq (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1:ℝ)))) :
    ‖f‖^2 = ∫ θ : AddCircle (1:ℝ), ‖f θ‖^2 ∂AddCircle.haarAddCircle := by
  have hh := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def f f)
  rw [← integral_re] at hh
  · simpa only [← norm_sq_eq_re_inner] using hh
  · exact L2.integrable_inner f f

/-- Finite Bessel inequality for the actual product Fourier coefficients.
The function may be merely square integrable, allowing a minor-arc indicator. -/
theorem markedProductFourier_bessel (S : Finset ℤ) {f : AddCircle (1:ℝ) → ℂ}
    (hf : MemLp f 2 AddCircle.haarAddCircle) :
    (∑ b : S, ‖∫ θ : AddCircle (1:ℝ),
      fourier (-b.1) θ * f θ ∂AddCircle.haarAddCircle‖^2) ≤
      ∫ θ : AddCircle (1:ℝ), ‖f θ‖^2 ∂AddCircle.haarAddCircle := by
  classical
  have hb := (orthonormal_fourier (T := (1:ℝ))).sum_inner_products_le
    (hf.toLp f) (s := S)
  have hc (b : ℤ) : inner ℂ (fourierLp (T := (1:ℝ)) 2 b) (hf.toLp f) =
      ∫ θ : AddCircle (1:ℝ), fourier (-b) θ * f θ ∂AddCircle.haarAddCircle := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_fourierLp (T := (1:ℝ)) 2 b,hf.coeFn_toLp] with θ hθ hfθ
    rw [hθ,hfθ]
    simp only [RCLike.inner_apply',fourier_neg]
  simp_rw [hc] at hb
  rw [markedProductL2_norm_sq] at hb
  have hi : (∫ θ : AddCircle (1:ℝ), ‖(hf.toLp f) θ‖^2 ∂AddCircle.haarAddCircle) =
      ∫ θ : AddCircle (1:ℝ), ‖f θ‖^2 ∂AddCircle.haarAddCircle :=
    integral_congr_ae (hf.coeFn_toLp.fun_comp (fun z : ℂ => ‖z‖^2))
  rw [hi] at hb
  rw [Finset.sum_coe_sort S (fun b : ℤ =>
    ‖∫ θ : AddCircle (1:ℝ), fourier (-b) θ * f θ ∂AddCircle.haarAddCircle‖^2)]
  exact hb

end ArtinMatthews
