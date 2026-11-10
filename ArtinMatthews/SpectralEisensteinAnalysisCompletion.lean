module

public import ArtinMatthews.SpectralEisensteinSeedAnalysis
public import ArtinMatthews.SpectralCompactDenseCore
public import ArtinMatthews.SpectralModularDensity
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

/-! The actual compact Eisenstein transform extends to all ambient L²
vectors with its proved operator bound and exact compact calibration. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace ArtinMatthews

theorem gamma0EisensteinAnalysis_exists (N : ℕ) [NeZero N] :
    ∃ A : Gamma0RegionL2 N →L[ℂ] Gamma0EisensteinSpectralSpace N,
      ∀ ψ : h2SmoothCompactSeeds,A (gamma0SmoothSeedMass N ψ)=gamma0EisensteinSeedAnalysis N ψ :=
  exists_bounded_extension_of_dense_functions (D:=h2SmoothCompactSeeds)
    (gamma0EisensteinSeedAnalysis N) (gamma0SmoothSeedMass N) (gamma0SmoothSeedMass_denseRange N)
    (gamma0EisensteinSeedAnalysis N).map_add (gamma0EisensteinSeedAnalysis N).map_smul
    (gamma0SmoothSeedMass N).map_add (gamma0SmoothSeedMass N).map_smul
    ⟨1,fun ψ => by simpa only [one_mul] using gamma0EisensteinSeedAnalysis_norm_le N ψ⟩

def gamma0EisensteinAnalysis (N : ℕ) [NeZero N] :
    Gamma0RegionL2 N →L[ℂ] Gamma0EisensteinSpectralSpace N :=
  (gamma0EisensteinAnalysis_exists N).choose

theorem gamma0EisensteinAnalysis_seed (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    gamma0EisensteinAnalysis N (gamma0SmoothSeedMass N ψ)=gamma0EisensteinSeedAnalysis N ψ :=
  (gamma0EisensteinAnalysis_exists N).choose_spec ψ

theorem gamma0EisensteinAnalysis_norm_le (N : ℕ) [NeZero N] (f : Gamma0RegionL2 N) :
    ‖gamma0EisensteinAnalysis N f‖≤‖f‖ := by
  apply isClosed_property (gamma0SmoothSeedMass_denseRange N)
    (isClosed_le (continuous_norm.comp (gamma0EisensteinAnalysis N).continuous) continuous_norm)
  intro ψ
  change ‖gamma0EisensteinAnalysis N (gamma0SmoothSeedMass N ψ)‖≤‖gamma0SmoothSeedMass N ψ‖
  rw [gamma0EisensteinAnalysis_seed]
  exact gamma0EisensteinSeedAnalysis_norm_le N ψ

theorem gamma0EisensteinAnalysis_opNorm_le (N : ℕ) [NeZero N] :
    ‖gamma0EisensteinAnalysis N‖≤1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun f => by simpa only [one_mul] using gamma0EisensteinAnalysis_norm_le N f)

theorem gamma0EisensteinAnalysis_compact_pair (N : ℕ) [NeZero N] (ψ ξ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0EisensteinAnalysis N (gamma0SmoothSeedMass N ψ))
      (gamma0EisensteinAnalysis N (gamma0SmoothSeedMass N ξ))=gamma0StoneEisensteinPair N ψ ξ := by
  rw [gamma0EisensteinAnalysis_seed,gamma0EisensteinAnalysis_seed]
  exact gamma0EisensteinSeedAnalysis_inner N ψ ξ

end ArtinMatthews
