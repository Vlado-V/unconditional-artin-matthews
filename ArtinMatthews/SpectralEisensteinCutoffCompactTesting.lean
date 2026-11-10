module

public import ArtinMatthews.SpectralEisensteinCompactCutoff
public import ArtinMatthews.SpectralEisensteinCompactForcing
public import ArtinMatthews.SpectralGamma0AmbientResolvent
public import ArtinMatthews.SpectralSectionLaplacianSeed
public import ArtinMatthews.SpectralEisensteinCutoffAutomorphy
public import ArtinMatthews.SpectralEisensteinCutoffRegularity
public import ArtinMatthews.SpectralEisensteinOutgoingCharts
public import ArtinMatthews.SpectralEisensteinWeakForcing
public import ArtinMatthews.SpectralGamma0EnergyPairing
public import ArtinMatthews.SpectralGamma0GlobalDifferentialForm
public import ArtinMatthews.SpectralGamma0MassRepresentativeUnfolding
public import ArtinMatthews.SpectralSectionC2Green
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Genuine entire compact test pairings of the literal Eisenstein cutoff,
with its exact compact-forcing weak equation on the whole upper half-plane. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace ContDiff
namespace ArtinMatthews

def gamma0EisensteinCutoffCompactTest (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (ψ : h2SmoothCompactSeeds) (s : ℂ) : ℂ :=
  ∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (gamma0CuspEisensteinCutoff N a s z)

theorem gamma0EisensteinCutoffCompactTest_analyticAt (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (ψ : h2SmoothCompactSeeds) (s : ℂ) :
    AnalyticAt ℂ (gamma0EisensteinCutoffCompactTest N a ψ) s := by
  let K := tsupport ψ.val
  have hK : IsCompact K := ψ.val.hasCompactSupport
  have hψ : MemLp (fun z : UpperHalfPlane => ψ.val z) 2 (volume.restrict K) :=
    spectralContinuous_memLp_compactRegion ψ.val ψ.val.continuous K hK
  let P := hψ.toLp (fun z => ψ.val z)
  let C := gamma0CuspEisensteinCutoffCompactMass N a 1 K hK
  have he (w : ℂ) : inner ℂ P (C w)=gamma0EisensteinCutoffCompactTest N a ψ w := by
    rw [L2.inner_def,gamma0EisensteinCutoffCompactTest]
    have hC : C w=ᵐ[volume.restrict K] gamma0CuspEisensteinCutoff N a w := by
      simpa only [C,inv_one,one_smul] using gamma0CuspEisensteinCutoffCompactMass_ae N a 1 K hK w
    calc
      _ = ∫ z in K, inner ℂ (ψ.val z) (gamma0CuspEisensteinCutoff N a w z) := by
        apply integral_congr_ae
        filter_upwards [hψ.coeFn_toLp,hC] with z hP hCz
        change inner ℂ (P z) (C w z)=_
        rw [hP,hCz]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport hz,inner_zero_left])
  rw [← funext he]
  exact ((innerSL ℂ P).analyticAt _).comp (gamma0CuspEisensteinCutoffCompactMass_analyticAt N a 1 K hK s)

theorem gamma0EisensteinCutoffCompactTest_forcing (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (ψ : h2SmoothCompactSeeds) (s : ℂ) :
    (2:ℂ)*gamma0EisensteinCutoffCompactTest N a (h2SectionLaplacianSeed ψ) s-
      s*(1-s)*((2:ℂ)*gamma0EisensteinCutoffCompactTest N a ψ s)=
      inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0CuspEisensteinCompactForcingMass N a s) := by
  let C := gamma0CuspEisensteinCutoff N a s
  let F := gamma0CuspEisensteinCompactForcing N a s
  have hC : Continuous C := gamma0CuspOutgoingCutoff_continuous N a s
  have hF : Continuous F := gamma0CuspEisensteinCompactForcing_continuous N a s
  have hC2 : ContDiffOn ℝ 2 (fun z : ℂ => C (UpperHalfPlane.ofComplex z)) {z | 0<z.im} :=
    (gamma0CuspEisensteinCutoff_spatial_smooth N a s).of_le (by simp)
  have ht := h2Section_laplacian_transfer_C2 ψ C hC2
  have hp (z : UpperHalfPlane) :
      inner ℂ (ψ.val z) (h2SectionPositiveLaplacian C z)=
        (s*(1-s))*inner ℂ (ψ.val z) (C z)+inner ℂ (ψ.val z) (F z) := by
    have hh := gamma0CuspEisensteinCutoff_laplacian_error N a s z
    change h2SectionPositiveLaplacian C z-s*(1-s)*C z=F z at hh
    have hh' : h2SectionPositiveLaplacian C z=s*(1-s)*C z+F z := by linear_combination hh
    rw [hh',inner_add_right]
    exact congrArg (fun w : ℂ => w+inner ℂ (ψ.val z) (F z))
      (inner_smul_right (𝕜 := ℂ) (E := ℂ) (ψ.val z) (C z) (s*(1-s)))
  simp_rw [hp] at ht
  rw [integral_add ((h2CompactInner_integrable ψ C hC).const_mul (s*(1-s)))
    (h2CompactInner_integrable ψ F hF),integral_const_mul] at ht
  rw [gamma0Mass_inner_unfold_representative N (gamma0CuspEisensteinCompactForcingMass N a s)
    F hF (gamma0CuspEisensteinCompactForcing_automorphy N a s)
    (gamma0CuspEisensteinCompactForcingMass_ae N a s) ψ]
  change (2:ℂ)*(∫ z : UpperHalfPlane, inner ℂ (h2SectionPositiveLaplacian ψ.val z) (C z))-
    (s*(1-s))*(2*(∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (C z)))=
      2*(∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (F z))
  linear_combination (2:ℂ)*ht

theorem gamma0Energy_test_mass_laplacian_of_pencil (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (z : ℂ) (u : gamma0EnergySpace N) (F : Gamma0RegionL2 N)
    (h : gamma0EnergyResolventPencil N z u=gamma0EnergyMassAdjoint N F) :
    inner ℂ (gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ)) (gamma0EnergyInclusion N u)-
      z*inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0EnergyInclusion N u)=
      inner ℂ (gamma0SmoothSeedMass N ψ) F := by
  have hf := gamma0Energy_completed_global_differential_pairing N ψ u
  rw [gamma0Energy_inner,gamma0EnergyInclusion_test,inner_add_left] at hf
  have hg := add_left_cancel hf
  have hp := congrArg (innerSL ℂ (gamma0EnergyTest N ψ)) h
  simp only [innerSL_apply_apply] at hp
  rwa [gamma0EnergyResolventPencil_inner,gamma0EnergyMassAdjoint_inner,
    gamma0EnergyInclusion_test,hg] at hp

end ArtinMatthews
