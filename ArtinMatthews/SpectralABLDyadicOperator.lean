module

public import ArtinMatthews.SpectralKLCompactIteration
public import ArtinMatthews.SpectralABLDyadicDerivative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Complex
open scoped ContDiff
noncomputable section

private theorem spectralDyadic_iteratedDeriv_smooth (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (d : ℕ) : ContDiff ℝ ∞ (iteratedDeriv d f) := by
  induction d with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ d ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

private theorem spectralDyadic_iteratedDeriv_add (f : ℝ → ℂ) (j d : ℕ) :
    iteratedDeriv j (iteratedDeriv d f) = iteratedDeriv (j+d) f := by
  ext x
  simp only [iteratedDeriv_eq_iterate,Function.iterate_add_apply]

/-- Each differential monomial of the shifted K operator costs at most
two powers of the source derivative scale. -/
theorem spectralDyadic_monomial_deriv_bound (a d J : ℕ) (hda : d ≤ a) (ha : a ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Z M : ℝ) (f : ℝ → ℂ),
      0 < X → 1 ≤ Z → X ≤ Z → 0 ≤ M → ContDiff ℝ ∞ f →
      (∀ j ≤ J+2, ∀ x ∈ Icc X (2*X), (X/Z)^j*‖iteratedDeriv j f x‖ ≤ M) →
      ∀ j ≤ J, ∀ x ∈ Icc X (2*X),
        (X/Z)^j*‖iteratedDeriv j (fun y : ℝ => (y : ℂ)^a*iteratedDeriv d f y) x‖ ≤ C*Z^2*M := by
  let φ : ℝ → ℂ := fun x => (x : ℂ)^a
  have hφ : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.pow a
  obtain ⟨C,hC,hbound⟩ := spectralDyadic_scaled_mul_deriv_bound φ hφ.contDiffOn J
  refine ⟨C,hC,?_⟩
  intro X Z M f hX hZ hXZ hM hf hF j hj x hx
  let b : ℝ := X/Z
  have hZ' : 0 < Z := zero_lt_one.trans_le hZ
  have hb : 0 < b := div_pos hX hZ'
  have hbX : b ≤ X := div_le_self hX.le hZ
  have hfd := spectralDyadic_iteratedDeriv_smooth f hf d
  have hF' (i : ℕ) (hi : i ≤ J) (y : ℝ) (hy : y ∈ Icc X (2*X)) :
      b^i*‖iteratedDeriv i (iteratedDeriv d f) y‖ ≤ M/b^d := by
    apply (le_div_iff₀ (pow_pos hb _)).mpr
    rw [spectralDyadic_iteratedDeriv_add]
    calc
      _ = b^(i+d)*‖iteratedDeriv (i+d) f y‖ := by rw [pow_add]; ring
      _ ≤ _ := hF (i+d) (by omega) y hy
  have hprod := hbound X b (M/b^d) (iteratedDeriv d f) hX hb.le hbX
    (by positivity) hfd hF' j hj x hx
  have heq : (fun y : ℝ => (y : ℂ)^a*iteratedDeriv d f y) =
      fun y => (X : ℂ)^a*(φ (y/X)*iteratedDeriv d f y) := by
    funext y
    dsimp [φ]
    push_cast
    rw [← mul_assoc,← mul_pow,mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hX.ne')]
  have hbPow : b^d*Z^d = X^d := by
    rw [← mul_pow,show b*Z = X from div_mul_cancel₀ _ hZ'.ne']
  have hratio : X^a/b^d ≤ Z^2 := by
    have hr : X^a/b^d = X^(a-d)*Z^d := (div_eq_iff (pow_ne_zero _ hb.ne')).mpr (by
      calc
        _ = X^(a-d)*X^d := by rw [← pow_add,Nat.sub_add_cancel hda]
        _ = _ := by rw [← hbPow]; ring)
    calc
      _ = X^(a-d)*Z^d := hr
      _ ≤ Z^(a-d)*Z^d := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hX.le hXZ _) (by positivity)
      _ = Z^a := by rw [← pow_add,Nat.sub_add_cancel hda]
      _ ≤ _ := pow_le_pow_right₀ hZ ha
  change b^j*‖iteratedDeriv j (fun y : ℝ => (y : ℂ)^a*iteratedDeriv d f y) x‖ ≤ _
  rw [heq,iteratedDeriv_const_mul_field,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hX.le]
  calc
    _ = X^a*(b^j*‖iteratedDeriv j (fun y => φ (y/X)*iteratedDeriv d f y) x‖) := by ring
    _ ≤ X^a*(C*(M/b^d)) := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (C*M)*(X^a/b^d) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hratio (mul_nonneg hC.le hM)).trans_eq (by ring)

theorem spectralKLShiftedOperator_eq_monomials (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    spectralKLShiftedOperator f = fun x =>
      f x - (x : ℂ)*iteratedDeriv 1 f x - (x : ℂ)^2*iteratedDeriv 2 f x + (x : ℂ)^2*f x := by
  funext x
  have hEmb : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := Complex.ofRealCLM.hasDerivAt
  have hDf := ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp) x).hasDerivAt
  have hflux := (hEmb.mul hDf).deriv
  change deriv (spectralKLCompactFlux f) x = _ at hflux
  simp only [spectralKLShiftedOperator,spectralKLPhysicalOperator,hflux,iteratedDeriv_succ',
    iteratedDeriv_zero]
  ring

theorem spectralKLShiftedOperator_dyadic_deriv (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Z M : ℝ) (f : ℝ → ℂ),
      0 < X → 1 ≤ Z → X ≤ Z → 0 ≤ M → ContDiff ℝ ∞ f →
      (∀ j ≤ J+2, ∀ x ∈ Icc X (2*X), (X/Z)^j*‖iteratedDeriv j f x‖ ≤ M) →
      ∀ j ≤ J, ∀ x ∈ Icc X (2*X),
        (X/Z)^j*‖iteratedDeriv j (spectralKLShiftedOperator f) x‖ ≤ C*Z^2*M := by
  obtain ⟨C₁,hC₁,h₁⟩ := spectralDyadic_monomial_deriv_bound 1 1 J (by decide) (by decide)
  obtain ⟨C₂,hC₂,h₂⟩ := spectralDyadic_monomial_deriv_bound 2 2 J (by decide) (by decide)
  obtain ⟨C₃,hC₃,h₃⟩ := spectralDyadic_monomial_deriv_bound 2 0 J (by decide) (by decide)
  refine ⟨1+C₁+C₂+C₃,by positivity,?_⟩
  intro X Z M f hX hZ hXZ hM hf hF j hj x hx
  let b := X/Z
  let f₁ : ℝ → ℂ := fun x => (x : ℂ)*iteratedDeriv 1 f x
  let f₂ : ℝ → ℂ := fun x => (x : ℂ)^2*iteratedDeriv 2 f x
  let f₃ : ℝ → ℂ := fun x => (x : ℂ)^2*f x
  have hf₁ : ContDiff ℝ ∞ f₁ := Complex.ofRealCLM.contDiff.mul (spectralDyadic_iteratedDeriv_smooth f hf _)
  have hf₂ : ContDiff ℝ ∞ f₂ := (Complex.ofRealCLM.contDiff.pow 2).mul (spectralDyadic_iteratedDeriv_smooth f hf _)
  have hf₃ : ContDiff ℝ ∞ f₃ := (Complex.ofRealCLM.contDiff.pow 2).mul hf
  have hf₁' : ContDiff ℝ ∞ (f-f₁) := hf.sub hf₁
  have hf₁₂ : ContDiff ℝ ∞ (f-f₁-f₂) := hf₁'.sub hf₂
  have heq : spectralKLShiftedOperator f = (f-f₁-f₂)+f₃ := spectralKLShiftedOperator_eq_monomials f hf
  have hA := hF j (by omega) x hx
  have hB : b^j*‖iteratedDeriv j f₁ x‖ ≤ C₁*Z^2*M := by
    simpa only [b,f₁,pow_one] using h₁ X Z M f hX hZ hXZ hM hf hF j hj x hx
  have hC : b^j*‖iteratedDeriv j f₂ x‖ ≤ C₂*Z^2*M := h₂ X Z M f hX hZ hXZ hM hf hF j hj x hx
  have hD : b^j*‖iteratedDeriv j f₃ x‖ ≤ C₃*Z^2*M := by
    simpa only [b,f₃,iteratedDeriv_zero] using h₃ X Z M f hX hZ hXZ hM hf hF j hj x hx
  have hb : 0 ≤ b := div_nonneg hX.le (zero_le_one.trans hZ)
  have hzM : M ≤ Z^2*M := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ (n := 2) hZ) hM
  change b^j*‖iteratedDeriv j (spectralKLShiftedOperator f) x‖ ≤ _
  rw [heq,iteratedDeriv_add (hf₁₂.contDiffAt.of_le (by simp))
    (hf₃.contDiffAt.of_le (by simp)),iteratedDeriv_sub (hf₁'.contDiffAt.of_le (by simp))
    (hf₂.contDiffAt.of_le (by simp)),iteratedDeriv_sub (hf.contDiffAt.of_le (by simp))
    (hf₁.contDiffAt.of_le (by simp))]
  have hn := (norm_add_le (iteratedDeriv j f x-iteratedDeriv j f₁ x-iteratedDeriv j f₂ x)
    (iteratedDeriv j f₃ x)).trans (add_le_add
      ((norm_sub_le (iteratedDeriv j f x-iteratedDeriv j f₁ x) (iteratedDeriv j f₂ x)).trans
        (add_le_add (norm_sub_le _ _) (le_refl _))) (le_refl _))
  calc
    _ ≤ b^j*(‖iteratedDeriv j f x‖+‖iteratedDeriv j f₁ x‖+‖iteratedDeriv j f₂ x‖+
        ‖iteratedDeriv j f₃ x‖) := mul_le_mul_of_nonneg_left hn (pow_nonneg hb _)
    _ = b^j*‖iteratedDeriv j f x‖+b^j*‖iteratedDeriv j f₁ x‖+b^j*‖iteratedDeriv j f₂ x‖+
        b^j*‖iteratedDeriv j f₃ x‖ := by ring
    _ ≤ Z^2*M+C₁*Z^2*M+C₂*Z^2*M+C₃*Z^2*M :=
      add_le_add (add_le_add (add_le_add (hA.trans hzM) hB) hC) hD
    _ = _ := by ring

end
end ArtinMatthews
