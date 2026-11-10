module

public import ArtinMatthews.SpectralEisensteinHeightProfileCalculus
public import ArtinMatthews.SpectralEisensteinCutoffSmooth
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

/-! Genuine hyperbolic gradients of normalized height profiles. The row
gradient has norm |H rho'(H)|, independently of the matrix representative. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem h2SectionGradient_of_plane (F : UpperHalfPlane → ℂ) (U : ℝ×ℝ → ℂ)
    (hU : ∀ p (hp : 0 < p.2), U p=F ⟨Complex.mk p.1 p.2,hp⟩)
    (z : UpperHalfPlane) (a b : ℂ)
    (hD : HasFDerivAt U (spectralPlaneDerivative a b) (z.re,z.im)) :
    h2SectionGradient F z=WithLp.toLp 2 ![z.im*a,z.im*b] := by
  have he : (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) =ᶠ[𝓝 (z:ℂ)]
      fun w => U (Complex.equivRealProdCLM w) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos] with w hw
    rw [hU _ hw,UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    rfl
  have hd := hD.comp (z:ℂ) Complex.equivRealProdCLM.hasFDerivAt
  have hd' := he.fderiv_eq.trans hd.fderiv
  ext i
  fin_cases i <;> simp [h2SectionGradient,hd',spectralPlaneDerivative_apply,Complex.real_smul]

def eisensteinHeightProfileGradient (w c d : ℝ) (f : ℝ → ℂ) (p : ℝ×ℝ) :
    EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![p.2*eisensteinHeightProfileX w c d f p,
    p.2*eisensteinHeightProfileY w c d f p]

theorem eisensteinHeightProfileGradient_norm (w c d : ℝ) (hw : 0 < w)
    (hcd : c ≠ 0 ∨ d ≠ 0) (f : ℝ → ℂ) (p : ℝ×ℝ) (hp : 0 < p.2) :
    ‖eisensteinHeightProfileGradient w c d f p‖=
      eisensteinNormalizedRowHeight w c d p*‖deriv f (eisensteinNormalizedRowHeight w c d p)‖ := by
  have hH : 0 < eisensteinNormalizedRowHeight w c d p := by
    unfold eisensteinNormalizedRowHeight
    positivity
  have hg := eisensteinNormalizedRowHeight_grad_sq w c d hcd p hp
  have he : ‖eisensteinHeightProfileGradient w c d f p‖^2=
      (eisensteinNormalizedRowHeight w c d p*‖deriv f (eisensteinNormalizedRowHeight w c d p)‖)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [eisensteinHeightProfileGradient,WithLp.ofLp_toLp,Fin.sum_univ_two,
      Matrix.cons_val_zero,Matrix.cons_val_one,eisensteinHeightProfileX,eisensteinHeightProfileY,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
    calc
      _=p.2^2*‖deriv f (eisensteinNormalizedRowHeight w c d p)‖^2*
          ((eisensteinNormalizedRowHeightX w c d p)^2+(eisensteinNormalizedRowHeightY w c d p)^2) := by ring
      _=_ := by rw [hg];field_simp
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hH.le (norm_nonneg _))).mp he

def cuspEisensteinProfileTerm (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (f : ℝ → ℂ)
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) : ℂ :=
  f (cuspEisensteinNormalizedHeight N r a v z)

theorem cuspEisensteinProfileTerm_plane (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (f : ℝ → ℂ) (v : Gamma0CuspEisensteinRows N r a) (p : ℝ×ℝ) (hp : 0 < p.2) :
    eisensteinHeightProfilePlane (gamma0CuspTrueWidth N a) (v.val 0) (v.val 1) f p=
      cuspEisensteinProfileTerm N r a f v ⟨Complex.mk p.1 p.2,hp⟩ := by
  unfold eisensteinHeightProfilePlane cuspEisensteinProfileTerm
  rw [eisensteinNormalizedRowHeight_eq _ _ _ (cuspEisensteinRow_coefficients_ne_zero N r a v) p hp]
  exact congrArg f (cuspEisensteinNormalizedHeightPlane_eq N r a v p hp)

theorem cuspEisensteinProfileTerm_smooth (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (v : Gamma0CuspEisensteinRows N r a) :
    ContDiffOn ℝ ∞ (fun w : ℂ => cuspEisensteinProfileTerm N r a f v (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im} := by
  have hc := (hf.comp_contDiffOn (cuspEisensteinNormalizedHeightPlane_smooth N r a v)).comp
    Complex.equivRealProdCLM.contDiff.contDiffOn
    (show MapsTo Complex.equivRealProdCLM {w : ℂ | 0 < w.im} {p : ℝ×ℝ | 0 < p.2} by
      intro w hw;exact hw)
  apply hc.congr
  intro w hw
  simp only [Function.comp_apply]
  rw [cuspEisensteinNormalizedHeightPlane_eq N r a v (Complex.equivRealProdCLM w) hw,
    UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  rfl

theorem cuspEisensteinProfileTerm_gradient (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    h2SectionGradient (cuspEisensteinProfileTerm N r a f v) z=
      eisensteinHeightProfileGradient (gamma0CuspTrueWidth N a) (v.val 0) (v.val 1) f (z.re,z.im) := by
  exact h2SectionGradient_of_plane _ _ (cuspEisensteinProfileTerm_plane N r a f v) z _ _
    (eisensteinHeightProfile_hasFDerivAt _ _ _ (cuspEisensteinRow_coefficients_ne_zero N r a v)
      f hf _ z.im_pos)

theorem cuspEisensteinProfileTerm_gradient_norm (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    ‖h2SectionGradient (cuspEisensteinProfileTerm N r a f v) z‖=
      cuspEisensteinNormalizedHeight N r a v z*‖deriv f (cuspEisensteinNormalizedHeight N r a v z)‖ := by
  rw [cuspEisensteinProfileTerm_gradient N r a f hf v z,
    eisensteinHeightProfileGradient_norm _ _ _ (by exact_mod_cast gamma0CuspTrueWidth_pos N a)
      (cuspEisensteinRow_coefficients_ne_zero N r a v) f _ z.im_pos]
  have he := eisensteinNormalizedRowHeight_eq (gamma0CuspTrueWidth N a) (v.val 0) (v.val 1)
    (cuspEisensteinRow_coefficients_ne_zero N r a v) (z.re,z.im) z.im_pos
  have he' := cuspEisensteinNormalizedHeightPlane_eq N r a v (z.re,z.im) z.im_pos
  have hH : eisensteinNormalizedRowHeight (gamma0CuspTrueWidth N a) (v.val 0) (v.val 1) (z.re,z.im)=
      cuspEisensteinNormalizedHeight N r a v z := by
    convert he.trans he' using 1
    congr 1
  rw [hH]

end ArtinMatthews
