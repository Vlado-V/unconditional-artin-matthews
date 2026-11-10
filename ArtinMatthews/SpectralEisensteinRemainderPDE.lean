module

public import ArtinMatthews.SpectralEisensteinCompactForcing
public import ArtinMatthews.SpectralCuspEisensteinPDE
public import ArtinMatthews.SpectralEisensteinCutoffRegularity
public import ArtinMatthews.SpectralPlaneLaplacianLinearity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual truncated Eisenstein remainder solves the literal forced
hyperbolic equation. No resolvent agreement is used in this calculation. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem spectralPlanePositiveHyperbolic_sub (F G : ℝ×ℝ → ℂ)
    (hF : ContDiffOn ℝ 2 F {p | 0 < p.2}) (hG : ContDiffOn ℝ 2 G {p | 0 < p.2})
    (p : ℝ×ℝ) (hp : 0 < p.2) :
    spectralPlanePositiveHyperbolic (F-G) p=
      spectralPlanePositiveHyperbolic F p-spectralPlanePositiveHyperbolic G p := by
  have h := spectralPlanePositiveHyperbolic_finset_sum (Finset.univ : Finset (Fin 2)) ![F,(-1:ℂ) • G]
    (fun i _ => by fin_cases i;exact hF;exact (contDiffOn_const : ContDiffOn ℝ 2
      (fun _ : ℝ×ℝ => (-1:ℂ)) {p | 0 < p.2}).mul hG) p hp
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] at h
  rw [spectralPlanePositiveHyperbolic_smul (-1) G hG p hp] at h
  change spectralPlanePositiveHyperbolic (fun q => F q-G q) p=_
  simpa only [neg_one_smul,sub_eq_add_neg,neg_one_mul,Pi.neg_apply] using h

theorem spectralSectionPlane_C2 (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) {z | 0 < z.im}) :
    ContDiffOn ℝ 2 (spectralSectionPlane F) {p : ℝ×ℝ | 0 < p.2} := by
  apply hF.comp Complex.equivRealProdCLM.symm.contDiff.contDiffOn
  intro p hp
  change 0 < p.2 at hp
  change 0 < (Complex.equivRealProdCLM.symm p).im
  simpa only [Complex.equivRealProdCLM_symm_apply,Complex.add_im,Complex.ofReal_im,
    Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
    zero_mul,add_zero,zero_add] using hp

theorem h2SectionPositiveLaplacian_sub_C2 (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) {z | 0 < z.im})
    (hG : ContDiffOn ℝ 2 (fun z : ℂ => G (UpperHalfPlane.ofComplex z)) {z | 0 < z.im})
    (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (F-G) z=
      h2SectionPositiveLaplacian F z-h2SectionPositiveLaplacian G z :=
  spectralPlanePositiveHyperbolic_sub _ _ (spectralSectionPlane_C2 F hF)
    (spectralSectionPlane_C2 G hG) _ z.im_pos

theorem gamma0CuspEisensteinRemainder_classical_forcing (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (gamma0CuspEisensteinRemainder N a s) z-
      s*(1-s)*gamma0CuspEisensteinRemainder N a s z=
        -gamma0CuspEisensteinCompactForcing N a s z := by
  have hc := gamma0CuspEisensteinCutoff_laplacian_error N a s z
  have hE := gamma0CuspEisenstein_classical_eigen_pde N a s hs z
  have hG := gamma0CuspEisensteinCutoff_spatial_smooth N a s
  change h2SectionPositiveLaplacian
    ((gamma0CuspEisenstein N a s)-(gamma0CuspEisensteinCutoff N a s)) z-
      s*(1-s)*(gamma0CuspEisenstein N a s z-gamma0CuspEisensteinCutoff N a s z)=_
  rw [h2SectionPositiveLaplacian_sub_C2 _ _ (gamma0CuspEisenstein_spatial_C2 N a s hs)
    (hG.of_le (by simp)) z,hE]
  linear_combination -hc

end ArtinMatthews
