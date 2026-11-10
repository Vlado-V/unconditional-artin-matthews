module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralBarnesFirstLemma
public import ArtinMatthews.SpectralBesselProductMellin
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The actual K_nu K_mu Mellin integral has the closed four-Gamma value.
All convergence and convolution inputs come from the checked preceding packet. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem schlafliBesselK_product_mellin_closed_on_line (ν μ s : ℂ) (σ : ℝ)
    (hμ : |μ.re| < σ) (hν : |ν.re| < s.re-σ) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*schlafliBesselK ν x*schlafliBesselK μ x) =
      ((2 : ℂ)^(s-3) * Complex.Gamma ((s-ν-μ)/2) * Complex.Gamma ((s+ν-μ)/2) *
        Complex.Gamma ((s-ν+μ)/2) * Complex.Gamma ((s+ν+μ)/2)) / Complex.Gamma s := by
  let a : ℂ := ((σ : ℂ)-μ)/2
  let b : ℂ := ((σ : ℂ)+μ)/2
  let c : ℂ := (s-(σ : ℂ)-ν)/2
  let d : ℂ := (s-(σ : ℂ)+ν)/2
  have ha : 0 < a.re := by dsimp [a]; simp only [Complex.div_ofNat_re,Complex.sub_re,Complex.ofReal_re]; linarith [le_abs_self μ.re]
  have hb : 0 < b.re := by dsimp [b]; simp only [Complex.div_ofNat_re,Complex.add_re,Complex.ofReal_re]; linarith [neg_le_abs μ.re]
  have hc : 0 < c.re := by dsimp [c]; simp only [Complex.div_ofNat_re,Complex.sub_re,Complex.ofReal_re]; linarith [le_abs_self ν.re]
  have hd : 0 < d.re := by dsimp [d]; simp only [Complex.div_ofNat_re,Complex.add_re,Complex.sub_re,Complex.ofReal_re]; linarith [neg_le_abs ν.re]
  have hpoint (t : ℝ) :
      spectralKMellinMultiplier ν (s-((σ : ℂ)+(t : ℂ)*Complex.I)) *
        spectralKMellinMultiplier μ ((σ : ℂ)+(t : ℂ)*Complex.I) =
      (2 : ℂ)^(s-4)*spectralBarnesIntegrand a b c d (t/2) := by
    have hp : (2 : ℂ)^((s-((σ : ℂ)+(t : ℂ)*Complex.I))-2) *
        (2 : ℂ)^(((σ : ℂ)+(t : ℂ)*Complex.I)-2) = (2 : ℂ)^(s-4) := by
      rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      congr 1
      ring
    have h1 : (((σ : ℂ)+(t : ℂ)*Complex.I)-μ)/2 = a+(t/2 : ℝ)*Complex.I := by dsimp [a]; push_cast; ring
    have h2 : (((σ : ℂ)+(t : ℂ)*Complex.I)+μ)/2 = b+(t/2 : ℝ)*Complex.I := by dsimp [b]; push_cast; ring
    have h3 : ((s-((σ : ℂ)+(t : ℂ)*Complex.I))-ν)/2 = c-(t/2 : ℝ)*Complex.I := by dsimp [c]; push_cast; ring
    have h4 : ((s-((σ : ℂ)+(t : ℂ)*Complex.I))+ν)/2 = d-(t/2 : ℝ)*Complex.I := by dsimp [d]; push_cast; ring
    unfold spectralKMellinMultiplier spectralBarnesIntegrand
    rw [h1,h2,h3,h4]
    calc
      _ = ((2 : ℂ)^((s-((σ : ℂ)+(t : ℂ)*Complex.I))-2) *
          (2 : ℂ)^(((σ : ℂ)+(t : ℂ)*Complex.I)-2)) *
        (Complex.Gamma (a+(t/2 : ℝ)*Complex.I)*Complex.Gamma (b+(t/2 : ℝ)*Complex.I)*
          Complex.Gamma (c-(t/2 : ℝ)*Complex.I)*Complex.Gamma (d-(t/2 : ℝ)*Complex.I)) := by ring
      _ = _ := by rw [hp]
  have hscale : (∫ t : ℝ, spectralBarnesIntegrand a b c d (t/2)) =
      (2 : ℝ) • ∫ t : ℝ, spectralBarnesIntegrand a b c d t := by
    simpa using Measure.integral_comp_div (spectralBarnesIntegrand a b c d) 2
  have hBarnes := spectral_barnes_first_lemma a b c d ha hb hc hd
  have hA : a+c = (s-ν-μ)/2 := by dsimp [a,c]; ring
  have hB : a+d = (s+ν-μ)/2 := by dsimp [a,d]; ring
  have hC : b+c = (s-ν+μ)/2 := by dsimp [b,c]; ring
  have hD : b+d = (s+ν+μ)/2 := by dsimp [b,d]; ring
  have hS : a+b+c+d = s := by dsimp [a,b,c,d]; ring
  rw [hA,hB,hC,hD,hS] at hBarnes
  have htwo : 2*(2 : ℂ)^(s-4) = (2 : ℂ)^(s-3) := by
    calc
      _ = (2 : ℂ)^(1 : ℂ)*(2 : ℂ)^(s-4) := by rw [Complex.cpow_one]
      _ = (2 : ℂ)^(1+(s-4)) := (Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)).symm
      _ = _ := by congr 1; ring
  rw [schlafliBesselK_product_mellin_convolution ν μ s σ hμ hν]
  simp_rw [hpoint]
  rw [integral_const_mul,hscale]
  simp only [Complex.real_smul] at hBarnes ⊢
  norm_num only [Complex.ofReal_ofNat] at hBarnes ⊢
  calc
    _ = (2*(2 : ℂ)^(s-4)) *
        ((((1/(2*Real.pi) : ℝ) : ℂ)) * ∫ t : ℝ, spectralBarnesIntegrand a b c d t) := by ring
    _ = _ := by rw [htwo,hBarnes]; ring

theorem schlafliBesselK_product_mellin_closed (ν μ s : ℂ) (hs : |ν.re|+|μ.re| < s.re) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*schlafliBesselK ν x*schlafliBesselK μ x) =
      ((2 : ℂ)^(s-3) * Complex.Gamma ((s-ν-μ)/2) * Complex.Gamma ((s+ν-μ)/2) *
        Complex.Gamma ((s-ν+μ)/2) * Complex.Gamma ((s+ν+μ)/2)) / Complex.Gamma s :=
  schlafliBesselK_product_mellin_closed_on_line ν μ s (spectralKProductMellinLine ν μ s)
    (spectralKProductMellinLine_bounds ν μ s hs).1
    (spectralKProductMellinLine_bounds ν μ s hs).2

end ArtinMatthews
