module

public import ArtinMatthews.SourceArchWeightedScatteringParameter
public import ArtinMatthews.SourceArchScatteringGram
public import ArtinMatthews.SourceArchScatteringAffine
public import ArtinMatthews.SourceArchTranslatedKernel
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact diagonal normalization of the Fourier kernel, with parameter
derivatives and joint continuity on the positive height half-space. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory Filter Matrix
open ArtinMatthews.VaryingKummerAnalytic
open scoped MatrixGroups Topology
noncomputable section

def sourceArchWeightedDiagonalProfile (ψ : ℂ → ℂ) (s a : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ (1-2*s) * sourceArchWeightedScattering ψ s (a*(r:ℂ))

def sourceArchWeightedDiagonalProfileDerivative (ψ : ℂ → ℂ) (s a : ℂ) (r : ℝ) : ℂ :=
  ((r : ℂ) ^ (1-2*s) * ((Real.log r : ℂ)*(-2))) *
      sourceArchWeightedScattering ψ s (a*(r:ℂ)) +
    (r : ℂ) ^ (1-2*s) * sourceArchWeightedScatteringDerivative ψ s (a*(r:ℂ))

theorem sourceArchWeightedDiagonalProfile_eq_integral (ψ : ℂ → ℂ) (s a : ℂ) (y : ℂˣ) :
    sourceArchWeightedDiagonalProfile ψ s a ‖(y : ℂ)‖ =
      ∫ x : ℂ, ψ (a*x) *
        sourceArchSphericalSection s (sourcePGL2Weyl*sourcePGL2Upper x*sourcePGL2Diagonal y)
        ∂sourceComplexTraceMeasure := by
  let r := ‖(y : ℂ)‖
  have hr : 0 < r := norm_pos_iff.mpr y.ne_zero
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hh : sourceArchHeight (sourceGL2Diagonal y) = r := by
    simp [sourceArchHeight,sourceArchBottomNorm,sourceGL2Diagonal,
      GeneralLinearGroup.val_det_apply,Matrix.det_fin_two,r]
  have hg : sourceArchGramShift (sourceGL2Diagonal y) = 0 := by
    simp [sourceArchGramShift,sourceArchBottomNorm,sourceGL2Diagonal]
  have hform (x : ℂ) :
      ψ (a*x)*sourceArchSphericalSection s
        (sourcePGL2Weyl*sourcePGL2Upper x*sourcePGL2Diagonal y) =
      (r:ℂ)^(-(2*s+1)) *
        (ψ (a*(r:ℂ)*(x/(r:ℂ))) * sourceArchScatteringKernel s (x/(r:ℂ))) := by
    rw [sourceArchSphericalSection_translated s (sourceGL2Diagonal y),
      sourceArchAffineCoordinate,hh,hg,add_zero]
    rw [show a*(r:ℂ)*(x/(r:ℂ)) = a*x by field_simp]
    ring
  simp_rw [hform]
  rw [integral_const_mul]
  have hi := sourceArchTraceIntegral_affine
    (fun x => ψ (a*(r:ℂ)*x)*sourceArchScatteringKernel s x) 0 hr
  simp only [add_zero] at hi
  rw [hi,← mul_assoc]
  change (r:ℂ)^(1-2*s)*sourceArchWeightedScattering ψ s (a*(r:ℂ)) =
    (r:ℂ)^(-(2*s+1)) * ((r^2:ℝ):ℂ) * sourceArchWeightedScattering ψ s (a*(r:ℂ))
  congr 1
  rw [Complex.ofReal_pow,← Complex.cpow_two,← Complex.cpow_add _ _ hr0]
  congr 1
  ring

theorem sourceArchWeightedDiagonalProfile_hasDerivAt (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hψ₁ : ∀ x, ‖ψ x‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) (a : ℂ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun z => sourceArchWeightedDiagonalProfile ψ z a r)
      (sourceArchWeightedDiagonalProfileDerivative ψ s a r) s := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have h₁ := ((hasDerivAt_const s (1:ℂ)).sub ((hasDerivAt_id s).const_mul 2)).const_cpow
    (c := (r:ℂ)) (Or.inl hr0)
  have h₂ := sourceArchWeightedScattering_hasDerivAt ψ hψ hψ₁ hs (a*(r:ℂ))
  have h := h₁.mul h₂
  convert h using 1
  · funext z
    rfl
  · simp only [sourceArchWeightedDiagonalProfileDerivative,Pi.sub_apply,id_eq,mul_one,zero_sub,
      ← Complex.ofReal_log hr.le]
    ring

theorem sourceArchWeightedDiagonalProfile_continuousAt (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hψ₁ : ∀ x, ‖ψ x‖ ≤ 1) (p : ℂ × ℂ × ℝ)
    (hs : 0 < p.1.re) (hr : 0 < p.2.2) :
    ContinuousAt (fun p : ℂ × ℂ × ℝ => sourceArchWeightedDiagonalProfile ψ p.1 p.2.1 p.2.2) p := by
  have hheight : Continuous (fun p : ℂ × ℂ × ℝ => (p.2.2:ℂ)) :=
    Complex.continuous_ofReal.comp continuous_snd.snd
  have hexponent : Continuous (fun p : ℂ × ℂ × ℝ => (1:ℂ)-2*p.1) :=
    continuous_const.sub (continuous_const.mul continuous_fst)
  have hc := hheight.continuousAt.cpow hexponent.continuousAt
    (Complex.ofReal_mem_slitPlane.mpr hr)
  have harg : Continuous (fun p : ℂ × ℂ × ℝ => (p.1,p.2.1*(p.2.2:ℂ))) :=
    continuous_fst.prodMk (continuous_snd.fst.mul (Complex.continuous_ofReal.comp continuous_snd.snd))
  have hlocal := sourceArchWeightedScattering_continuousAt ψ hψ hψ₁
    (p.1,p.2.1*(p.2.2:ℂ)) hs
  have hw := hlocal.comp (f := fun r : ℂ × ℂ × ℝ => (r.1,r.2.1*(r.2.2:ℂ))) (harg.continuousAt (x := p))
  exact hc.mul hw

theorem sourceArchWeightedDiagonalProfileDerivative_continuousAt (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hψ₁ : ∀ x, ‖ψ x‖ ≤ 1) (p : ℂ × ℂ × ℝ)
    (hs : 0 < p.1.re) (hr : 0 < p.2.2) :
    ContinuousAt (fun p : ℂ × ℂ × ℝ => sourceArchWeightedDiagonalProfileDerivative ψ p.1 p.2.1 p.2.2) p := by
  have hheight : Continuous (fun p : ℂ × ℂ × ℝ => (p.2.2:ℂ)) :=
    Complex.continuous_ofReal.comp continuous_snd.snd
  have hexponent : Continuous (fun p : ℂ × ℂ × ℝ => (1:ℂ)-2*p.1) :=
    continuous_const.sub (continuous_const.mul continuous_fst)
  have hc := hheight.continuousAt.cpow hexponent.continuousAt
    (Complex.ofReal_mem_slitPlane.mpr hr)
  have hy : Continuous (fun p : ℂ × ℂ × ℝ => p.2.2) := continuous_snd.snd
  have hl := hy.continuousAt.log hr.ne'
  have hlC := Complex.continuous_ofReal.continuousAt.comp hl
  have hlog := hlC.mul_const (-2:ℂ)
  have harg : Continuous (fun p : ℂ × ℂ × ℝ => (p.1,p.2.1*(p.2.2:ℂ))) :=
    continuous_fst.prodMk (continuous_snd.fst.mul (Complex.continuous_ofReal.comp continuous_snd.snd))
  have hw := (sourceArchWeightedScattering_continuousAt ψ hψ hψ₁
    (p.1,p.2.1*(p.2.2:ℂ)) hs).comp (f := fun r : ℂ × ℂ × ℝ => (r.1,r.2.1*(r.2.2:ℂ))) (harg.continuousAt (x := p))
  have hw' := (sourceArchWeightedScatteringDerivative_continuousAt ψ hψ hψ₁
    (p.1,p.2.1*(p.2.2:ℂ)) hs).comp (f := fun r : ℂ × ℂ × ℝ => (r.1,r.2.1*(r.2.2:ℂ))) (harg.continuousAt (x := p))
  exact ((hc.mul hlog).mul hw).add (hc.mul hw')

end
end ArtinMatthews.SourceArchJacquet
