module

public import ArtinMatthews.SpectralGamma0EllipticEigenLocal
public import ArtinMatthews.SpectralGamma0EigenPointBound
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

/-! Compact-set polynomial evaluation bounds for the actual eigenbasis. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0FullCuspidalSpectralBasis_compact_real_bound
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (L0 : ℂ →L[ℝ] ℝ)
    {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ spectralEllipticOpenStrip (2*(N:ℝ)) Y) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Gamma0AllHeightSpectralIndex N) (u : (Fin 2 → ℝ) → ℝ),
      ContDiffOn ℝ ∞ u (spectralEllipticOpenStrip (2*(N:ℝ)) Y) →
      (∀ᵐ z ∂volume, z ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y →
        u z = L0 (gamma0CuspTwoCellCoordinateRestriction N r Y hY
          (gamma0FullCuspidalSpectralBasis N i).val (spectralEllipticCoordinates z))) →
      ∀ z ∈ K, ‖u z‖ ≤ C*(1+gamma0AllHeightGradientSpectralValue N i) := by
  classical
  have hlocal := fun x : K => gamma0FullCuspidalSpectralBasis_local_real_point_bound
    N r Y hY L0 (hKΩ x.property)
  choose V C hV hxV hVΩ hC hb using hlocal
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V hV (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩)
  have hsum : 0 ≤ ∑ x ∈ s, C x := Finset.sum_nonneg (fun x _ => (hC x).le)
  refine ⟨(∑ x ∈ s, C x)+1,by linarith,?_⟩
  intro i u hu hueq z hz
  obtain ⟨x,hxs,hxz⟩ := mem_iUnion₂.mp (hs hz)
  have hle : C x ≤ (∑ y ∈ s, C y)+1 :=
    (Finset.single_le_sum (fun y _ => (hC y).le) hxs).trans (le_add_of_nonneg_right zero_le_one)
  exact (hb x i u hu hueq z hxz).trans (mul_le_mul_of_nonneg_right hle
    (by linarith [gamma0AllHeightGradientSpectralValue_nonneg N i]))

theorem gamma0FullCuspidalSpectralBasis_compact_complex_bound
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ spectralEllipticOpenStrip (2*(N:ℝ)) Y) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Gamma0AllHeightSpectralIndex N) (F : (Fin 2 → ℝ) → ℂ),
      ContDiffOn ℝ ∞ F (spectralEllipticOpenStrip (2*(N:ℝ)) Y) →
      (∀ᵐ z ∂volume, z ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y →
        F z = gamma0CuspTwoCellCoordinateRestriction N r Y hY
          (gamma0FullCuspidalSpectralBasis N i).val (spectralEllipticCoordinates z)) →
      ∀ z ∈ K, ‖F z‖ ≤ C*(1+gamma0AllHeightGradientSpectralValue N i) := by
  obtain ⟨Cr,hCr,hr⟩ := gamma0FullCuspidalSpectralBasis_compact_real_bound N r Y hY Complex.reCLM hK hKΩ
  obtain ⟨Ci,hCi,hi⟩ := gamma0FullCuspidalSpectralBasis_compact_real_bound N r Y hY Complex.imCLM hK hKΩ
  refine ⟨Cr+Ci,add_pos hCr hCi,?_⟩
  intro i F hF hFae z hz
  have hFr : ContDiffOn ℝ ∞ (fun x => (F x).re) (spectralEllipticOpenStrip (2*(N:ℝ)) Y) :=
    Complex.reCLM.contDiff.comp_contDiffOn hF
  have hFi : ContDiffOn ℝ ∞ (fun x => (F x).im) (spectralEllipticOpenStrip (2*(N:ℝ)) Y) :=
    Complex.imCLM.contDiff.comp_contDiffOn hF
  have hr' := hr i (fun x => (F x).re) hFr
    (hFae.mono fun x hx hxs => congrArg Complex.re (hx hxs)) z hz
  have hi' := hi i (fun x => (F x).im) hFi
    (hFae.mono fun x hx hxs => congrArg Complex.im (hx hxs)) z hz
  have hn : ‖F z‖ ≤ ‖(F z).re‖+‖(F z).im‖ := by
    simpa only [Real.norm_eq_abs] using Complex.norm_le_abs_re_add_abs_im (F z)
  exact (hn.trans (add_le_add hr' hi')).trans_eq (by ring)

end ArtinMatthews
