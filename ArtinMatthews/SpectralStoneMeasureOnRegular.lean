module

public import ArtinMatthews.SpectralStoneBoundaryDensity
public import ArtinMatthews.SpectralCompactOpenExtension
public import ArtinMatthews.SpectralStoneCompactTestDensity
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

/-! The actual scalar spectral measure on the open regular energies is
the genuine measure with the computed density, obtained by Riesz uniqueness. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported ENNReal
namespace ArtinMatthews

theorem spectralMeasure_comap_eq_density_of_compact_tests (μ : Measure ℝ) [IsFiniteMeasure μ]
    (U : Set ℝ) (hU : IsOpen U) (g : ℝ → ℝ) (hg : ContinuousOn g U)
    (hgn : ∀ x ∈ U, 0 ≤ g x)
    (hTest : ∀ f : C_c(ℝ,ℝ), tsupport f⊆U →
      (∫ x,f x ∂μ)=∫ x : ℝ,g x*f x) :
    Measure.comap ((↑) : U → ℝ) μ =
      (Measure.comap ((↑) : U → ℝ) volume).withDensity (fun x : U => ENNReal.ofReal (g x)) := by
  let m := Measure.comap ((↑) : U → ℝ) μ
  let v := Measure.comap ((↑) : U → ℝ) volume
  let ρ (x : U) := g x
  let ν := v.withDensity (fun x : U => ENNReal.ofReal (ρ x))
  have hρ : Continuous ρ := hg.domRestrict
  let _ : LocallyCompactSpace U := hU.locallyCompactSpace
  have hE := MeasurableEmbedding.subtype_coe hU.measurableSet
  let _ : IsFiniteMeasure m := by unfold m;infer_instance
  let _ : IsFiniteMeasureOnCompacts v := IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val hE
  let _ : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hρ
  change m=ν
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let F := spectralCompactOpenExtension hU f
  have hF (x : U) : F x=f x := spectralCompactOpenExtensionValue_apply f x
  have hF0 (x : ℝ) (hx : x∉U) : F x=0 := spectralCompactOpenExtensionValue_zero f hx
  have hl : (∫ x,f x ∂m)=∫ x,F x ∂μ := by
    calc
      _ = ∫ x : U,F x ∂m :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hF x).symm)
      _ = ∫ x in U,F x ∂μ := by
        rw [← map_comap_subtype_coe hU.measurableSet μ]
        exact (hE.integral_map (fun x : ℝ => F x)).symm
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero hF0
  have hr : (∫ x,f x ∂ν)=∫ x : ℝ,g x*F x := by
    calc
      _ = ∫ x : U,ρ x*f x ∂v := by
        rw [show ν=v.withDensity (fun x : U => ENNReal.ofReal (ρ x)) from rfl,
          integral_withDensity_eq_integral_toReal_smul hρ.measurable.ennreal_ofReal
            (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (fun x : U => f x)]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change (ENNReal.ofReal (ρ x)).toReal • f x=ρ x*f x
          rw [ENNReal.toReal_ofReal (hgn x x.property),smul_eq_mul]
      _ = ∫ x : U,g x*F x ∂v :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          change g x*f x=g x*F x
          rw [hF x])
      _ = ∫ x in U,g x*F x := by
        rw [← map_comap_subtype_coe hU.measurableSet volume]
        exact (hE.integral_map (fun x : ℝ => g x*F x)).symm
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        change g x*F x=0
        rw [hF0 x hx,mul_zero])
  exact hl.trans ((hTest F (spectralCompactOpenExtension_tsupport hU f)).trans hr.symm)

def gamma0StoneContinuousMeasure (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) : Measure ℝ :=
  let U := gamma0StoneGoodEnergy N ψ Y
  Measure.map ((↑) : U → ℝ)
    ((Measure.comap ((↑) : U → ℝ) volume).withDensity
      (fun x : U => ENNReal.ofReal (gamma0StoneBoundaryDensity N ψ Y x)))

theorem gamma0AmbientSpectralMeasure_restrict_good (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) :
    (gamma0AmbientSpectralMeasure N (gamma0SmoothSeedMass N ψ)).restrict (gamma0StoneGoodEnergy N ψ Y)=
      gamma0StoneContinuousMeasure N ψ Y := by
  let μ := gamma0AmbientSpectralMeasure N (gamma0SmoothSeedMass N ψ)
  let U := gamma0StoneGoodEnergy N ψ Y
  have hU := gamma0StoneGoodEnergy_open N ψ Y
  rw [← map_comap_subtype_coe hU.measurableSet μ]
  exact congrArg (Measure.map ((↑) : U → ℝ))
    (spectralMeasure_comap_eq_density_of_compact_tests μ U hU _ (gamma0StoneBoundaryDensity_continuousOn N ψ Y)
      (gamma0StoneBoundaryDensity_nonneg N ψ Y) (gamma0AmbientStone_compactTest_density N ψ Y))

end ArtinMatthews
