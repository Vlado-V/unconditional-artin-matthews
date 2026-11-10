module

public import ArtinMatthews.SpectralGamma0CuspMassRestriction
public import ArtinMatthews.SpectralGamma0CompactMass
public import ArtinMatthews.SpectralModularDensity
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

/-! On an actual modular mass chart, the patch moved into the infinity
strip has the same restriction as the completed infinity mass. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0InfinityChartPatch_ae_zero (N : ℕ) [NeZero N]
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (γ : CongruenceSubgroup.Gamma0 N)
    (Y : ℝ) (hY : 0 < Y) (f : Gamma0RegionL2 N)
    (hz : gamma0CuspMassRestriction N 1 Y hY f = 0) :
    (f q : UpperHalfPlane → ℂ) =ᵐ[(volume.restrict ModularGroup.fd).restrict
      ((fun z : UpperHalfPlane => ((γ : SL(2, ℤ)) * q.out⁻¹) • z) ⁻¹'
        hyperbolicCuspStrip (N : ℝ) Y)] (fun _ => 0) := by
  let g : SL(2, ℤ) := (γ : SL(2, ℤ)) * q.out⁻¹
  let A : UpperHalfPlane → UpperHalfPlane := fun z => g • z
  let S := hyperbolicCuspStrip (N : ℝ) Y
  let μ := (volume : Measure UpperHalfPlane).restrict (A ⁻¹' S)
  let ν := ((volume : Measure UpperHalfPlane).restrict ModularGroup.fd).restrict (A ⁻¹' S)
  have hleft : ν ≤ volume.restrict ModularGroup.fd := Measure.restrict_le_self
  have hright : ν ≤ μ := Measure.restrict_mono_measure Measure.restrict_le_self _
  have hA : MeasurableEmbedding A := by
    change MeasurableEmbedding (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ g • z)
    exact measurableEmbedding_const_smul _
  have hp : MeasurePreserving A μ (volume.restrict S) :=
    (h2_integer_measurePreserving g).restrict_preimage_emb hA S
  let P : CuspHyperbolicL2 (N : ℝ) Y →ₗᵢ[ℂ] Lp ℂ 2 μ :=
    Lp.compMeasurePreservingₗᵢ ℂ A hp
  let L (F : Gamma0RegionL2 N) := spectralLpMeasureRestriction hleft (F q)
  let R (F : Gamma0RegionL2 N) := spectralLpMeasureRestriction hright
    (P (gamma0CuspMassRestriction N 1 Y hY F))
  have hL : Continuous L := (spectralLpMeasureRestriction hleft).continuous.comp
    (PiLp.continuous_apply 2 _ q)
  have hR : Continuous R := (spectralLpMeasureRestriction hright).continuous.comp
    (P.continuous.comp (gamma0CuspMassRestriction N 1 Y hY).continuous)
  have he : L f = R f := by
    apply isClosed_property (gamma0SmoothSeedMass_denseRange N) (isClosed_eq hL hR)
    intro ψ
    apply Lp.ext
    have hl := spectralLpMeasureRestriction_ae hleft (gamma0SmoothSeedMass N ψ q)
    have hq := (Measure.absolutelyContinuous_of_le hleft).ae_eq (gamma0SeedMass_coeFn N ψ.val q)
    let F := gamma0CuspMassRestriction N 1 Y hY (gamma0SmoothSeedMass N ψ)
    have hr := spectralLpMeasureRestriction_ae hright (P F)
    have hcomp := (Measure.absolutelyContinuous_of_le hright).ae_eq
      (Lp.coeFn_compMeasurePreserving F hp)
    have hsrc := (Measure.absolutelyContinuous_of_le hright).ae_eq
      (hp.quasiMeasurePreserving.ae_eq_comp (gamma0CuspMassRestriction_seed_ae N 1 Y hY ψ))
    filter_upwards [hl, hq, hr, hcomp, hsrc] with z h₁ h₂ h₃ h₄ h₅
    change L (gamma0SmoothSeedMass N ψ) z = R (gamma0SmoothSeedMass N ψ) z
    calc
      _ = (gamma0SmoothSeedMass N ψ q : UpperHalfPlane → ℂ) z := h₁
      _ = gamma0PoincareSeed N ψ.val (q.out⁻¹ • z) := h₂
      _ = gamma0CuspSection N ψ 1 (A z) := by
        simp only [gamma0CuspSection, inv_one, one_smul, A, g, mul_smul]
        exact (gamma0PoincareSeed_invariant N ψ.val γ (q.out⁻¹ • z)).symm
      _ = F (A z) := h₅.symm
      _ = P F z := h₄.symm
      _ = _ := h₃.symm
  have hLzero : L f = 0 := by
    rw [he]
    simp only [R, hz, map_zero]
  have hae := spectralLpMeasureRestriction_ae hleft (f q)
  change L f =ᵐ[ν] (f q : UpperHalfPlane → ℂ) at hae
  rw [hLzero] at hae
  exact hae.symm.trans (Lp.coeFn_zero ℂ 2 ν)

end ArtinMatthews
