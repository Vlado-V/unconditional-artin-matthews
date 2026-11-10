module

public import ArtinMatthews.SpectralGamma0EllipticEigenLocal
public import ArtinMatthews.SpectralEllipticH2Evaluation
public import ArtinMatthews.SpectralEllipticH2Pointwise
public import ArtinMatthews.SpectralGamma0EigenEnergyBounds
public import ArtinMatthews.SpectralGamma0EigenH2Bound
public import ArtinMatthews.SpectralGamma0EllipticBandCutoff
public import ArtinMatthews.SpectralGamma0EllipticBandIdentification
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Order.CompletePartialOrder
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
public import OAI.Analysis.PDE.Weak.Elliptic.CutoffExistence


set_option backward.privateInPublic true
@[expose] public section

/-! Actual polynomial point bounds on a fixed neighborhood, uniform in the spectral index. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational
namespace ArtinMatthews

theorem gamma0FullCuspidalSpectralBasis_local_real_point_bound
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (L0 : ℂ →L[ℝ] ℝ)
    {x : Fin 2 → ℝ} (hx : x ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y) :
    ∃ (V : Set (Fin 2 → ℝ)) (C : ℝ), IsOpen V ∧ x ∈ V ∧
      V ⊆ spectralEllipticOpenStrip (2*(N:ℝ)) Y ∧ 0 < C ∧
      ∀ (i : Gamma0AllHeightSpectralIndex N) (u : (Fin 2 → ℝ) → ℝ),
        ContDiffOn ℝ ∞ u (spectralEllipticOpenStrip (2*(N:ℝ)) Y) →
        (∀ᵐ z ∂volume, z ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y →
          u z = L0 (gamma0CuspTwoCellCoordinateRestriction N r Y hY
            (gamma0FullCuspidalSpectralBasis N i).val (spectralEllipticCoordinates z))) →
        ∀ z ∈ V, ‖u z‖ ≤ C*(1+gamma0AllHeightGradientSpectralValue N i) := by
  let c := (Y+x 1)/2
  let d := x 1+1
  have hYc : Y < c := by dsimp [c]; linarith [hx.2.2]
  have hc : 0 < c := hY.trans hYc
  have hcx : c < x 1 := by dsimp [c]; linarith [hx.2.2]
  have hxd : x 1 < d := by dsimp [d]; linarith
  obtain ⟨A,a,b,φ,ha,hab,hφ,hplateau,_⟩ :=
    exists_spectralEllipticBand_cutoff (w := 2*(N:ℝ)) (c := c) (d := d)
      (by positivity) hc (hcx.le.trans hxd.le)
  let Ω := spectralEllipticOpenStrip (2*(N:ℝ)) Y ∩ {z : Fin 2 → ℝ | c < z 1 ∧ z 1 < d}
  have hΩ : IsOpen Ω := (spectralEllipticOpenStrip_isOpen _ _).inter
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
      (isOpen_lt (continuous_apply 1) continuous_const))
  have hxΩ : x ∈ Ω := ⟨hx,hcx,hxd⟩
  have hΩband : Ω ⊆ spectralEllipticCoordinates ⁻¹' spectralEllipticBand (2*(N:ℝ)) c d := by
    intro z hz
    exact ⟨⟨hz.1.1,hz.1.2.1.le⟩,hz.2.1.le,hz.2.2.le⟩
  obtain ⟨β,U,hU,hxU,hUΩ,hβ,hcβ,hsβ,hβrange,hβone⟩ := exists_cutoff_with_open_plateau hΩ hxΩ
  obtain ⟨η,V,hV,hxV,hVU,hη,hcη,hsη,hηrange,hηone⟩ := exists_cutoff_with_open_plateau hU hxU
  have hηM : ∀ z, |η z| ≤ 1 := fun z => by rw [abs_of_nonneg (hηrange z).1]; exact (hηrange z).2
  obtain ⟨K,hK⟩ := ((hasCompactSupport_cellGradient hcη).isCompact_range
    (continuous_cellGradient (hη.of_le (by simp)))).isBounded.exists_norm_le
  have hηK : ∀ z, ‖cellGradient η z‖ ≤ K := fun z => hK _ (mem_range_self z)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hηK 0)
  obtain ⟨D,hD⟩ := ((hcη.fderiv (𝕜 := ℝ)).isCompact_range
    (hη.continuous_fderiv (by simp))).isBounded.exists_norm_le
  have hηD : ∀ z, ‖fderiv ℝ η z‖ ≤ D := fun z => hD _ (mem_range_self z)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hηD 0)
  obtain ⟨H,hH,hH2⟩ := gamma0FullCuspidalSpectralBasis_local_H2_bound φ ha hab hφ r L0 N
    hY hYc hplateau hΩ hΩband η hη hcη hK0 hD0 hηM hηK hηD (hsη.trans hUΩ)
  obtain ⟨S,hS,hpoint⟩ := spectralElliptic_H2_pointwise_bound hU η hη hcη hηM hsη
  let P := ‖gamma0EllipticPair φ ha hφ r L0 N‖
  let R := ‖gamma0EllipticMass φ ha hφ r L0 N‖
  have hP : 0 ≤ P := ContinuousLinearMap.opNorm_nonneg _
  have hR : 0 ≤ R := ContinuousLinearMap.opNorm_nonneg _
  refine ⟨V,S*(H+P+R+1),hV,hxV,hVU.trans (hUΩ.trans inter_subset_left),by positivity,?_⟩
  intro i u hu hueq z hz
  let p := gamma0EllipticPair φ ha hφ r L0 N (gamma0AllHeightSpectralEnergy N i).val
  let u0 := β*u
  have hu0 : ContDiff ℝ ∞ u0 := spectral_local_scalar_cutoff_smooth
    (spectralEllipticOpenStrip_isOpen _ _) u β hu hβ (hsβ.trans inter_subset_left)
  have hm : gamma0EnergyInclusion N (gamma0AllHeightSpectralEnergy N i).val =
      (gamma0FullCuspidalSpectralBasis N i).val := by
    rw [gamma0FullCuspidalSpectralBasis_coe]
    exact gamma0AllHeightSpectralEnergy_mass_ambient N i
  have hmass := gamma0EllipticMass_band_ae φ ha hab hφ r L0 N hY hYc hplateau
    (gamma0FullCuspidalSpectralBasis N i).val
  rw [← hm,gamma0EllipticMass_energy φ ha hab hφ r L0 N] at hmass
  rw [hm] at hmass
  have hband : MeasurableSet (spectralEllipticCoordinates ⁻¹' spectralEllipticBand (2*(N:ℝ)) c d) :=
    (spectralEllipticBand_measurable _ _ _).preimage spectralEllipticCoordinates.continuous.measurable
  have hpu : ∀ᵐ y ∂volume, y ∈ U → p.1 y = u0 y := by
    filter_upwards [(ae_restrict_iff' hband).mp hmass,hueq] with y hy hyu
    intro hyU
    have hyΩ := hUΩ hyU
    change p.1 y = β y*u y
    rw [hβone y hyU,one_mul]
    exact (hy (hΩband hyΩ)).trans (hyu hyΩ.1).symm
  obtain ⟨g,hg,hd⟩ := hH2 i 1
  have hb := hpoint p (gamma0EllipticPair_mem_H1Zero φ ha hφ r L0 N _) u0 hu0 hpu g hd z (hηone z hz)
  have hu0z : u0 z = u z := by
    change β z*u z = u z
    rw [hβone z (hVU hz),one_mul]
  rw [hu0z] at hb
  have hp2 : ‖p.2‖ ≤ P*(1+gamma0AllHeightGradientSpectralValue N i) :=
    (show ‖p.2‖ ≤ ‖p‖ from by rw [Prod.norm_def]; exact le_max_right _ _).trans
      (gamma0EllipticEigenPair_norm_le φ ha hφ r L0 N i)
  have hp1 : ‖p.1‖ ≤ R := gamma0EllipticEigenPair_mass_norm_le φ ha hab hφ r L0 N i
  have hlam := gamma0AllHeightGradientSpectralValue_nonneg N i
  have hp1' : ‖p.1‖ ≤ R*(1+gamma0AllHeightGradientSpectralValue N i) :=
    hp1.trans (by nlinarith)
  calc
    ‖u z‖ ≤ S*(‖g‖+‖p.2‖+‖p.1‖) := hb
    _ ≤ S*(H*(1+gamma0AllHeightGradientSpectralValue N i)+
        P*(1+gamma0AllHeightGradientSpectralValue N i)+R*(1+gamma0AllHeightGradientSpectralValue N i)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hg hp2) hp1') hS.le
    _ ≤ S*(H+P+R+1)*(1+gamma0AllHeightGradientSpectralValue N i) := by nlinarith

end ArtinMatthews
