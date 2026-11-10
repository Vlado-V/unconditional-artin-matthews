module

public import ArtinMatthews.SpectralGamma0EllipticEigenPlane
public import ArtinMatthews.SpectralGamma0SpectralCutoff
public import ArtinMatthews.SpectralGamma0EigenCompactBound
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

/-! Plane point bounds and finite spectral-window evaluation for the actual basis. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0FullCuspidalSpectralBasis_plane_compact_bound
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Gamma0AllHeightSpectralIndex N) (F : ℝ × ℝ → ℂ),
      ContDiffOn ℝ ∞ F {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2} →
      (∀ᵐ p ∂volume, (0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) →
        F p = gamma0CuspTwoCellCoordinateRestriction N r Y hY
          (gamma0FullCuspidalSpectralBasis N i).val p) →
      ∀ p ∈ K, ‖F p‖ ≤ C*(1+gamma0AllHeightGradientSpectralValue N i) := by
  let K0 := spectralEllipticCoordinates.symm '' K
  have hK0 : IsCompact K0 := hK.image spectralEllipticCoordinates.symm.continuous
  have hK0Ω : K0 ⊆ spectralEllipticOpenStrip (2*(N:ℝ)) Y := by
    rintro x ⟨p,hp,rfl⟩
    exact hKΩ hp
  obtain ⟨C,hC,hb⟩ := gamma0FullCuspidalSpectralBasis_compact_complex_bound N r Y hY hK0 hK0Ω
  refine ⟨C,hC,?_⟩
  intro i F hF hFae p hp
  let G := fun x => F (spectralEllipticCoordinates x)
  have hG : ContDiffOn ℝ ∞ G (spectralEllipticOpenStrip (2*(N:ℝ)) Y) :=
    hF.comp spectralEllipticCoordinates.contDiff.contDiffOn (fun _ hx => hx)
  have hGa : ∀ᵐ x ∂volume, x ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y →
      G x = gamma0CuspTwoCellCoordinateRestriction N r Y hY
        (gamma0FullCuspidalSpectralBasis N i).val (spectralEllipticCoordinates x) :=
    spectralEllipticCoordinates_measurePreserving.quasiMeasurePreserving.ae hFae
  have he := hb i G hG hGa (spectralEllipticCoordinates.symm p) ⟨p,hp,rfl⟩
  simpa only [G,ContinuousLinearEquiv.apply_symm_apply] using he

def gamma0FullCuspidalPlaneRepresentative (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (i : Gamma0AllHeightSpectralIndex N) : ℝ × ℝ → ℂ :=
  (gamma0FullCuspidalSpectralBasis_plane_smooth_periodic_classical N i r Y hY).choose

theorem gamma0FullCuspidalPlaneRepresentative_spec (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (i : Gamma0AllHeightSpectralIndex N) :
    ContDiffOn ℝ ∞ (gamma0FullCuspidalPlaneRepresentative N r Y hY i)
      {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2} ∧
    (∀ᵐ p ∂volume, (0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) →
      gamma0FullCuspidalPlaneRepresentative N r Y hY i p =
        gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0FullCuspidalSpectralBasis N i).val p) ∧
    (∀ p : ℝ × ℝ, (0 < p.1 ∧ p.1 < (N:ℝ) ∧ Y < p.2) →
      gamma0FullCuspidalPlaneRepresentative N r Y hY i (p.1+(N:ℝ),p.2) =
        gamma0FullCuspidalPlaneRepresentative N r Y hY i p) ∧
    ∀ p : ℝ × ℝ, (0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) →
      -(p.2^2) • (spectralPlaneSecond (gamma0FullCuspidalPlaneRepresentative N r Y hY i) 0 p +
        spectralPlaneSecond (gamma0FullCuspidalPlaneRepresentative N r Y hY i) 1 p) =
          (gamma0AllHeightGradientSpectralValue N i : ℂ)*gamma0FullCuspidalPlaneRepresentative N r Y hY i p :=
  (gamma0FullCuspidalSpectralBasis_plane_smooth_periodic_classical N i r Y hY).choose_spec

theorem gamma0FullCuspidalPlaneRepresentative_compact_bound (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Gamma0AllHeightSpectralIndex N) (p : ℝ × ℝ), p ∈ K →
      ‖gamma0FullCuspidalPlaneRepresentative N r Y hY i p‖ ≤
        C*(1+gamma0AllHeightGradientSpectralValue N i) := by
  obtain ⟨C,hC,hb⟩ := gamma0FullCuspidalSpectralBasis_plane_compact_bound N r Y hY hK hKΩ
  exact ⟨C,hC,fun i p hp => hb i _ (gamma0FullCuspidalPlaneRepresentative_spec N r Y hY i).1
    (gamma0FullCuspidalPlaneRepresentative_spec N r Y hY i).2.1 p hp⟩

theorem gamma0FullCuspidalPlaneRepresentative_window_sq_bound (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (p : ℝ × ℝ), p ∈ K →
      (∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R,
        ‖gamma0FullCuspidalPlaneRepresentative N r Y hY i p‖^2) ≤
        (gamma0AllHeightGradientSpectralCutoff N R).card*(C*(1+R))^2 := by
  obtain ⟨C,hC,hb⟩ := gamma0FullCuspidalPlaneRepresentative_compact_bound N r Y hY hK hKΩ
  refine ⟨C,hC,?_⟩
  intro R p hp
  calc
    _ ≤ ∑ _i ∈ gamma0AllHeightGradientSpectralCutoff N R, (C*(1+R))^2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (hb i p hp).trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl ((mem_gamma0AllHeightGradientSpectralCutoff N R i).mp hi)) hC.le)
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]

end ArtinMatthews
