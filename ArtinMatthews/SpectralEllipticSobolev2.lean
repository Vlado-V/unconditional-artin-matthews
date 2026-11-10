module

public import ArtinMatthews.SpectralPlaneSobolevL2
public import ArtinMatthews.SpectralGamma0EllipticBand
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded
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

/-! The quantitative H2 point estimate in the native two-coordinate chart. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
open OAI.Analysis.PDE.Weak
namespace ArtinMatthews

theorem spectralPlane_native_derivative (u : (Fin 2 → ℝ) → ℝ)
    (hu : ContDiff ℝ ∞ u) (j : Fin 2) (p : ℝ × ℝ) :
    fderiv ℝ (fun q => u (spectralEllipticCoordinates.symm q)) p (spectralPlaneDirection j) =
      coordinateDerivative u j (spectralEllipticCoordinates.symm p) := by
  have he := ((hu.differentiable (by simp) (spectralEllipticCoordinates.symm p)).hasFDerivAt.comp p
    spectralEllipticCoordinates.symm.hasFDerivAt).fderiv
  change (fderiv ℝ (u ∘ spectralEllipticCoordinates.symm) p) (spectralPlaneDirection j) = _
  rw [he]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
  rw [← spectralEllipticCoordinates_single,ContinuousLinearEquiv.symm_apply_apply]
  rfl

def spectralEllipticMixedLp (u : (Fin 2 → ℝ) → ℝ) (hu : ContDiff ℝ ∞ u)
    (hcu : HasCompactSupport u) : Lp ℝ 2 (volume : Measure (Fin 2 → ℝ)) :=
  ((contDiff_coordinateDerivative (contDiff_coordinateDerivative hu 0) 1).continuous.memLp_of_hasCompactSupport
    ((hcu.fderiv_apply ℝ (Pi.single 0 1)).fderiv_apply ℝ (Pi.single 1 1))).toLp
      (coordinateDerivative (coordinateDerivative u 0) 1)

theorem spectralEllipticMixedLp_plane (u : (Fin 2 → ℝ) → ℝ) (hu : ContDiff ℝ ∞ u)
    (hcu : HasCompactSupport u) :
    spectralPlaneMixedLp (fun p => u (spectralEllipticCoordinates.symm p))
      (hu.comp spectralEllipticCoordinates.symm.contDiff)
      (hcu.comp_homeomorph spectralEllipticCoordinates.symm.toHomeomorph) =
      spectralEllipticNativeToPlane (spectralEllipticMixedLp u hu hcu) := by
  have hx : spectralPlaneDx (fun p => u (spectralEllipticCoordinates.symm p)) =
      fun p => coordinateDerivative u 0 (spectralEllipticCoordinates.symm p) := by
    funext p
    exact spectralPlane_native_derivative u hu 0 p
  have hxy : spectralPlaneDy (spectralPlaneDx (fun p => u (spectralEllipticCoordinates.symm p))) =
      fun p => coordinateDerivative (coordinateDerivative u 0) 1 (spectralEllipticCoordinates.symm p) := by
    rw [hx]
    funext p
    exact spectralPlane_native_derivative (coordinateDerivative u 0) (contDiff_coordinateDerivative hu 0) 1 p
  apply Lp.ext
  have hr := spectralEllipticCoordinates_symm_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (show spectralEllipticMixedLp u hu hcu =ᵐ[volume]
      coordinateDerivative (coordinateDerivative u 0) 1 from MemLp.coeFn_toLp _)
  filter_upwards [show spectralPlaneMixedLp (fun p => u (spectralEllipticCoordinates.symm p))
      (hu.comp spectralEllipticCoordinates.symm.contDiff)
      (hcu.comp_homeomorph spectralEllipticCoordinates.symm.toHomeomorph) =ᵐ[volume]
      spectralPlaneDy (spectralPlaneDx (fun p => u (spectralEllipticCoordinates.symm p))) from MemLp.coeFn_toLp _,
    spectralEllipticNativeToPlane_ae (spectralEllipticMixedLp u hu hcu),hr] with p hp hq hs
  rw [hp,hxy,hq]
  simpa only [Function.comp_def] using hs.symm

theorem spectralElliptic_compact_sobolev_bound {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : (Fin 2 → ℝ) → ℝ) (hu : ContDiff ℝ ∞ u)
      (hcu : HasCompactSupport u), tsupport u ⊆ K → ∀ x,
      ‖u x‖ ≤ C*‖spectralEllipticMixedLp u hu hcu‖ := by
  obtain ⟨C,hC,hb⟩ := spectralPlane_compact_sobolev_bound (hK.image spectralEllipticCoordinates.continuous)
  refine ⟨C,hC,?_⟩
  intro u hu hcu hs x
  let v := fun p => u (spectralEllipticCoordinates.symm p)
  have hv := hu.comp spectralEllipticCoordinates.symm.contDiff
  have hcv := hcu.comp_homeomorph spectralEllipticCoordinates.symm.toHomeomorph
  have hvs : tsupport v ⊆ spectralEllipticCoordinates '' K := by
    change tsupport (u ∘ spectralEllipticCoordinates.symm.toHomeomorph) ⊆ _
    rw [tsupport_comp_eq_preimage u spectralEllipticCoordinates.symm.toHomeomorph]
    intro p hp
    exact ⟨spectralEllipticCoordinates.symm p,hs hp,ContinuousLinearEquiv.apply_symm_apply _ _⟩
  have ht := hb v hv hcv hvs (spectralEllipticCoordinates x)
  have hn : ‖spectralEllipticNativeToPlane (spectralEllipticMixedLp u hu hcu)‖ =
      ‖spectralEllipticMixedLp u hu hcu‖ :=
    (Lp.compMeasurePreservingₗᵢ ℝ spectralEllipticCoordinates.symm
      spectralEllipticCoordinates_symm_measurePreserving).norm_map _
  rw [spectralEllipticMixedLp_plane u hu hcu,hn] at ht
  simpa only [v,ContinuousLinearEquiv.symm_apply_apply] using ht

end ArtinMatthews
