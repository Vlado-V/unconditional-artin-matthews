module

public import ArtinMatthews.SpectralEisensteinHeightGeometry
public import ArtinMatthews.SpectralGamma0EisensteinPDE
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

/-! Actual chain rules for a smooth function of normalized cusp height. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace ArtinMatthews

def eisensteinHeightProfilePlane (w c d : ℝ) (f : ℝ → ℂ) (p : ℝ×ℝ) : ℂ :=
  f (eisensteinNormalizedRowHeight w c d p)

def eisensteinHeightProfileX (w c d : ℝ) (f : ℝ → ℂ) (p : ℝ×ℝ) : ℂ :=
  deriv f (eisensteinNormalizedRowHeight w c d p)*(eisensteinNormalizedRowHeightX w c d p:ℂ)

def eisensteinHeightProfileY (w c d : ℝ) (f : ℝ → ℂ) (p : ℝ×ℝ) : ℂ :=
  deriv f (eisensteinNormalizedRowHeight w c d p)*(eisensteinNormalizedRowHeightY w c d p:ℂ)

def eisensteinHeightProfileXX (w c d : ℝ) (f : ℝ → ℂ) (p : ℝ×ℝ) : ℂ :=
  deriv (deriv f) (eisensteinNormalizedRowHeight w c d p)*(eisensteinNormalizedRowHeightX w c d p:ℂ)^2+
    deriv f (eisensteinNormalizedRowHeight w c d p)*(eisensteinNormalizedRowHeightXX w c d p:ℂ)

def eisensteinHeightProfileXY (w c d : ℝ) (f : ℝ → ℂ) (p : ℝ×ℝ) : ℂ :=
  deriv (deriv f) (eisensteinNormalizedRowHeight w c d p)*
      (eisensteinNormalizedRowHeightX w c d p:ℂ)*(eisensteinNormalizedRowHeightY w c d p:ℂ)+
    deriv f (eisensteinNormalizedRowHeight w c d p)*(eisensteinNormalizedRowHeightXY w c d p:ℂ)

def eisensteinHeightProfileYY (w c d : ℝ) (f : ℝ → ℂ) (p : ℝ×ℝ) : ℂ :=
  deriv (deriv f) (eisensteinNormalizedRowHeight w c d p)*(eisensteinNormalizedRowHeightY w c d p:ℂ)^2+
    deriv f (eisensteinNormalizedRowHeight w c d p)*(eisensteinNormalizedRowHeightYY w c d p:ℂ)

theorem eisensteinHeightProfile_hasFDerivAt (w c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (p : ℝ×ℝ) (hp : 0 < p.2) :
    HasFDerivAt (eisensteinHeightProfilePlane w c d f)
      (spectralPlaneDerivative (eisensteinHeightProfileX w c d f p)
        (eisensteinHeightProfileY w c d f p)) p := by
  have h0 : HasDerivAt f (deriv f (eisensteinNormalizedRowHeight w c d p))
      (eisensteinNormalizedRowHeight w c d p) :=
    (hf.differentiable (by simp)).differentiableAt.hasDerivAt
  have h := h0.hasFDerivAt.comp p (eisensteinNormalizedRowHeight_hasFDerivAt w c d hcd p hp)
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro u
  simp [eisensteinHeightProfileX,eisensteinHeightProfileY,spectralPlaneDerivative,Complex.real_smul]
  ring

theorem eisensteinHeightProfileX_hasFDerivAt (w c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (p : ℝ×ℝ) (hp : 0 < p.2) :
    HasFDerivAt (eisensteinHeightProfileX w c d f)
      (spectralPlaneDerivative (eisensteinHeightProfileXX w c d f p)
        (eisensteinHeightProfileXY w c d f p)) p := by
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have h0 : HasDerivAt (deriv f) (deriv (deriv f) (eisensteinNormalizedRowHeight w c d p))
      (eisensteinNormalizedRowHeight w c d p) :=
    (hf1.differentiable (by simp)).differentiableAt.hasDerivAt
  have hD := h0.hasFDerivAt.comp p (eisensteinNormalizedRowHeight_hasFDerivAt w c d hcd p hp)
  have hX := Complex.ofRealCLM.hasFDerivAt.comp p
    (eisensteinNormalizedRowHeightX_hasFDerivAt w c d hcd p hp)
  convert! hD.mul hX using 1
  apply ContinuousLinearMap.ext
  intro u
  simp [eisensteinHeightProfileXX,eisensteinHeightProfileXY,spectralPlaneDerivative,Complex.real_smul]
  ring

theorem eisensteinHeightProfileY_hasFDerivAt (w c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (p : ℝ×ℝ) (hp : 0 < p.2) :
    HasFDerivAt (eisensteinHeightProfileY w c d f)
      (spectralPlaneDerivative (eisensteinHeightProfileXY w c d f p)
        (eisensteinHeightProfileYY w c d f p)) p := by
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have h0 : HasDerivAt (deriv f) (deriv (deriv f) (eisensteinNormalizedRowHeight w c d p))
      (eisensteinNormalizedRowHeight w c d p) :=
    (hf1.differentiable (by simp)).differentiableAt.hasDerivAt
  have hD := h0.hasFDerivAt.comp p (eisensteinNormalizedRowHeight_hasFDerivAt w c d hcd p hp)
  have hY := Complex.ofRealCLM.hasFDerivAt.comp p
    (eisensteinNormalizedRowHeightY_hasFDerivAt w c d hcd p hp)
  convert! hD.mul hY using 1
  apply ContinuousLinearMap.ext
  intro u
  simp [eisensteinHeightProfileXY,eisensteinHeightProfileYY,spectralPlaneDerivative,Complex.real_smul]
  ring

theorem eisensteinHeightProfile_second (w c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (p : ℝ×ℝ) (hp : 0 < p.2) :
    fderiv ℝ (fderiv ℝ (eisensteinHeightProfilePlane w c d f)) p=
      spectralPlaneDerivativeMap.comp
        ((spectralPlaneDerivative (eisensteinHeightProfileXX w c d f p)
          (eisensteinHeightProfileXY w c d f p)).prod
          (spectralPlaneDerivative (eisensteinHeightProfileXY w c d f p)
            (eisensteinHeightProfileYY w c d f p))) := by
  have he : fderiv ℝ (eisensteinHeightProfilePlane w c d f) =ᶠ[𝓝 p]
      fun q => spectralPlaneDerivative (eisensteinHeightProfileX w c d f q)
        (eisensteinHeightProfileY w c d f q) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with q hq
    exact (eisensteinHeightProfile_hasFDerivAt w c d hcd f hf q hq).fderiv
  rw [he.fderiv_eq]
  exact (hasFDerivAt_spectralPlaneDerivative
    (eisensteinHeightProfileX_hasFDerivAt w c d hcd f hf p hp)
    (eisensteinHeightProfileY_hasFDerivAt w c d hcd f hf p hp)).fderiv

theorem eisensteinHeightProfile_hyperbolic_pde (w c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (p : ℝ×ℝ) (hp : 0 < p.2) :
    -((p.2:ℂ)^2)*spectralPlaneHessianTrace
      (fderiv ℝ (fderiv ℝ (eisensteinHeightProfilePlane w c d f)) p)=
      -((eisensteinNormalizedRowHeight w c d p:ℂ)^2)*
        deriv (deriv f) (eisensteinNormalizedRowHeight w c d p) := by
  rw [eisensteinHeightProfile_second w c d hcd f hf p hp,spectralPlaneHessianTrace_apply]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    spectralPlaneDerivativeMap_apply,spectralPlaneDerivative_apply,one_smul,zero_smul,add_zero,zero_add]
  have hg := congrArg (fun t : ℝ => (t:ℂ)) (eisensteinNormalizedRowHeight_grad_sq w c d hcd p hp)
  have ht := congrArg (fun t : ℝ => (t:ℂ)) (eisensteinNormalizedRowHeight_trace_zero w c d hcd p hp)
  push_cast at hg ht
  unfold eisensteinHeightProfileXX eisensteinHeightProfileYY
  have hpC : (p.2:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  calc
    _=-((p.2:ℂ)^2)*(deriv (deriv f) (eisensteinNormalizedRowHeight w c d p)*
      ((eisensteinNormalizedRowHeightX w c d p:ℂ)^2+(eisensteinNormalizedRowHeightY w c d p:ℂ)^2)+
      deriv f (eisensteinNormalizedRowHeight w c d p)*
        ((eisensteinNormalizedRowHeightXX w c d p:ℂ)+(eisensteinNormalizedRowHeightYY w c d p:ℂ))) := by ring
    _=_ := by
      rw [hg,ht]
      field_simp
      ring

end ArtinMatthews
