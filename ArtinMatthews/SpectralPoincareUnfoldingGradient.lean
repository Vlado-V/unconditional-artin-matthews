module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import ArtinMatthews.SpectralGamma0Core
public import ArtinMatthews.SpectralSectionGradient
public import ArtinMatthews.SpectralModularDensityCharts
public import ArtinMatthews.SpectralPoincareUnfolding
public import ArtinMatthews.SpectralPoincareUnfoldingGradientSupport
public import ArtinMatthews.SpectralSectionGradientPairing
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

/-! Exact compact-seed unfolding of the actual complex Dirichlet pairing.
Both the finite gradient sum and the Möbius gradient covariance are proved
from the actual functions and their derivatives. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups CompactlySupported ContDiff

namespace ArtinMatthews

theorem gamma0_gradient_pairing_translate (N : ℕ)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    (hFinv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F ((γ : SL(2, ℤ)) • z) = F z)
    (ψ : h2SmoothCompactSeeds) (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    inner ℂ (h2SectionGradient (fun w => ψ.val ((γ : SL(2, ℤ)) • w)) z)
      (h2SectionGradient F z) =
      inner ℂ (h2SectionGradient ψ.val ((γ : SL(2, ℤ)) • z))
        (h2SectionGradient F ((γ : SL(2, ℤ)) • z)) := by
  have he : (fun w : UpperHalfPlane => F ((γ : SL(2, ℤ)) • w)) = F := funext (hFinv γ)
  have hc := h2SectionGradient_inner_pullback ψ.val F ψ.property hF
    (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ))) (by simp) z
  change inner ℂ (h2SectionGradient (fun w => ψ.val ((γ : SL(2, ℤ)) • w)) z)
    (h2SectionGradient (fun w => F ((γ : SL(2, ℤ)) • w)) z) = _ at hc
  rw [he] at hc
  exact hc

theorem gamma0_single_chart_gradient_integral (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    (hFinv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F ((γ : SL(2, ℤ)) • z) = F z)
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    (∫ z in ModularGroup.fd,
      inner ℂ (h2SectionGradient (gamma0PoincareSeed N ψ.val) (r⁻¹ • z))
        (h2SectionGradient F (r⁻¹ • z))) =
      ∑ᶠ γ : CongruenceSubgroup.Gamma0 N,
        ∫ z in ModularGroup.fd,
          inner ℂ (h2SectionGradient ψ.val ((γ : SL(2, ℤ)) • (r⁻¹ • z)))
            (h2SectionGradient F ((γ : SL(2, ℤ)) • (r⁻¹ • z))) := by
  classical
  let h : UpperHalfPlane → ℂ := fun z => inner ℂ (h2SectionGradient ψ.val z) (h2SectionGradient F z)
  have hc : Continuous h := (h2SectionGradient_continuous ψ.val ψ.property).inner
    (h2SectionGradient_continuous F hF)
  have hcomp : HasCompactSupport h := by
    apply ψ.val.hasCompactSupport.of_isClosed_subset (isClosed_tsupport h)
    apply closure_minimal _ (isClosed_tsupport _)
    intro z hz
    by_contra hn
    exact hz (by simp only [h, h2SectionGradient_eq_zero_of_notMem_tsupport ψ.val hn, inner_zero_left])
  obtain ⟨s, hsout, hsgrad⟩ := gamma0PoincareSeed_gradient_fd_eq_sum N ψ r
  have hint (γ : CongruenceSubgroup.Gamma0 N) :
      IntegrableOn (fun z : UpperHalfPlane => h ((γ : SL(2, ℤ)) • (r⁻¹ • z))) ModularGroup.fd := by
    let g := Matrix.SpecialLinearGroup.mapGL ℝ ((γ : SL(2, ℤ)) * r⁻¹)
    have hh : HasCompactSupport (h ∘ Homeomorph.smul g) := hcomp.comp_homeomorph _
    have hi : Integrable (h ∘ Homeomorph.smul g) (volume : Measure UpperHalfPlane) :=
      (hc.comp (continuous_const_smul g)).integrable_of_hasCompactSupport hh
    have hir := hi.restrict (s := ModularGroup.fd)
    change Integrable (fun z : UpperHalfPlane => h (((γ : SL(2, ℤ)) * r⁻¹) • z))
      (volume.restrict ModularGroup.fd) at hir
    simpa only [mul_smul, IntegrableOn] using hir
  have hsupp : Function.support (fun γ : CongruenceSubgroup.Gamma0 N =>
      ∫ z in ModularGroup.fd, h ((γ : SL(2, ℤ)) • (r⁻¹ • z))) ⊆ s := by
    intro γ hγ
    by_contra hn
    apply hγ
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    change h ((γ : SL(2, ℤ)) • (r⁻¹ • z)) = (0 : ℂ)
    simp only [h, h2SectionGradient_eq_zero_of_notMem_tsupport ψ.val (hsout γ hn z hz), inner_zero_left]
  calc
    _ = ∫ z in ModularGroup.fd, ∑ γ ∈ s, h ((γ : SL(2, ℤ)) • (r⁻¹ • z)) := by
      apply integral_congr_ae
      filter_upwards [modular_fdo_ae_on_fd] with z hz
      rw [hsgrad z hz, sum_inner]
      apply Finset.sum_congr rfl
      intro γ _
      exact gamma0_gradient_pairing_translate N F hF hFinv ψ γ (r⁻¹ • z)
    _ = ∑ γ ∈ s, ∫ z in ModularGroup.fd, h ((γ : SL(2, ℤ)) • (r⁻¹ • z)) :=
      integral_finsetSum s fun γ _ => hint γ
    _ = _ := (finsum_eq_sum_of_support_subset _ hsupp).symm

theorem gamma0_periodization_unfold_gradient_integral (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    (hFinv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F ((γ : SL(2, ℤ)) • z) = F z)
    (ψ : h2SmoothCompactSeeds) :
    (∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      ∫ z in ModularGroup.fd,
        inner ℂ (h2SectionGradient (gamma0PoincareSeed N ψ.val) (q.out⁻¹ • z))
          (h2SectionGradient F (q.out⁻¹ • z))) =
      2 * ∫ z, inner ℂ (h2SectionGradient ψ.val z) (h2SectionGradient F z) := by
  let h : UpperHalfPlane → ℂ := fun z => inner ℂ (h2SectionGradient ψ.val z) (h2SectionGradient F z)
  have hc : Continuous h := (h2SectionGradient_continuous ψ.val ψ.property).inner
    (h2SectionGradient_continuous F hF)
  have hcomp : HasCompactSupport h := by
    apply ψ.val.hasCompactSupport.of_isClosed_subset (isClosed_tsupport h)
    apply closure_minimal _ (isClosed_tsupport _)
    intro z hz
    by_contra hn
    exact hz (by simp only [h, h2SectionGradient_eq_zero_of_notMem_tsupport ψ.val hn, inner_zero_left])
  calc
    _ = ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ∑ᶠ γ : CongruenceSubgroup.Gamma0 N,
          ∫ z in ModularGroup.fd, h ((γ : SL(2, ℤ)) • (q.out⁻¹ • z)) :=
      Finset.sum_congr rfl fun q _ => gamma0_single_chart_gradient_integral N F hF hFinv ψ q.out
    _ = _ := gamma0_coset_translate_integral_unfold N h hc hcomp

end ArtinMatthews
