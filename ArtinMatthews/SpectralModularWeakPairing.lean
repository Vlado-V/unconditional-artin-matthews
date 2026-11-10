module

public import ArtinMatthews.SpectralSectionWeakPairing
public import Mathlib.NumberTheory.Modular
public import ArtinMatthews.SpectralGamma0CompactMass
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Actual weak-gradient pairings on each pulled-back modular chart.
The gradient remains the original-frame gradient already used in the energy
space; both test coefficients are pulled back with the chart. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

/-- Exact change of variables for an actual integrand supported in a
pulled-back modular region. -/
theorem h2_integer_supported_integral (r : SL(2, ℤ)) (f : UpperHalfPlane → ℂ)
    (hf : ∀ z : UpperHalfPlane, r • z ∉ ModularGroup.fd → f z = 0) :
    (∫ z in ModularGroup.fd, f (r⁻¹ • z)) = ∫ z, f z := by
  have hmp := h2_integer_measurePreserving r
  have hme : MeasurableEmbedding (fun z : UpperHalfPlane => r • z) := by
    change MeasurableEmbedding (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ r • z)
    exact measurableEmbedding_const_smul _
  have he := hmp.setIntegral_preimage_emb hme
    (fun z : UpperHalfPlane => f (r⁻¹ • z)) ModularGroup.fd
  simp only [inv_smul_smul] at he
  rw [← he]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hf

/-- Exact finite-coset chart weak pairing for an actual smooth section.
These are precisely the value and gradient representatives in the existing
Γ₀ energy graph; the test has actual compact support in the chart. -/
theorem h2_section_modular_weak_pairing {Y : ℝ} (hY : 0 < Y)
    (r : SL(2, ℤ)) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ)
    (hheight : tsupport φ ⊆ {p : ℝ × ℝ | Y < p.2})
    (hchart : ∀ p ∈ tsupport φ,
      r • UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p) ∈ ModularGroup.fd)
    (i : Fin 2) :
    (∫ z in ModularGroup.fd, (r⁻¹ • z).im^2 •
      (F (r⁻¹ • z) * fderiv ℝ φ ((r⁻¹ • z).re,(r⁻¹ • z).im) (spectralPlaneDirection i))) =
      -∫ z in ModularGroup.fd, h2SectionGradient F (r⁻¹ • z) i *
        ((r⁻¹ • z).im • φ ((r⁻¹ • z).re,(r⁻¹ • z).im)) := by
  have hout (z : UpperHalfPlane) (hz : r • z ∉ ModularGroup.fd) :
      (z.re,z.im) ∉ tsupport φ := by
    intro hp
    have hc : Complex.equivRealProdCLM.symm (z.re,z.im) = (z : ℂ) :=
      Complex.equivRealProdCLM.symm_apply_apply (z : ℂ)
    have hh := hchart (z.re,z.im) hp
    rw [hc,UpperHalfPlane.ofComplex_apply] at hh
    exact hz hh
  have hleft := h2_integer_supported_integral r
    (fun z => z.im^2 • (F z*fderiv ℝ φ (z.re,z.im) (spectralPlaneDirection i)))
    (fun z hz => by
      have hd : fderiv ℝ φ (z.re,z.im) (spectralPlaneDirection i) = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun p => fderiv ℝ φ p (spectralPlaneDirection i))
          (fun hp => hout z hz (tsupport_fderiv_apply_subset ℝ (spectralPlaneDirection i) hp))
      rw [hd,mul_zero,smul_zero])
  have hright := h2_integer_supported_integral r
    (fun z => h2SectionGradient F z i*(z.im • φ (z.re,z.im)))
    (fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (hout z hz),smul_zero,mul_zero])
  rw [hleft,hright]
  exact h2_section_weak_pairing hY F hF φ hφ hs hheight i

end ArtinMatthews
