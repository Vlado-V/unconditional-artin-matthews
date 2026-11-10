module

public import ArtinMatthews.SpectralHilbertBasisMultiplier
public import ArtinMatthews.SpectralEnergyTest
public import ArtinMatthews.SpectralGamma0CuspidalProjection
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

/-! Bounded energy tests acting on the actual complete cuspidal basis. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace ArtinMatthews

local instance cuspidalTest_inner (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜:=ℂ) (E:=Gamma0RegionL2 N) (gamma0AllHeightCuspidalMassSpace N)

def gamma0CuspidalTestCore (N : ℕ) [NeZero N] (h : SpectralEnergyTest) :
    gamma0AllHeightCuspidalMassSpace N →L[ℂ] gamma0AllHeightCuspidalMassSpace N :=
  spectralHilbertMultiplier (gamma0FullCuspidalSpectralBasis N) (gamma0CuspidalTestSymbol N h)
    ‖h‖ (norm_nonneg _) (gamma0CuspidalTestSymbol_bound N h)

def gamma0CuspidalTestOperator (N : ℕ) [NeZero N] (h : SpectralEnergyTest) :
    Gamma0RegionL2 N →L[ℂ] Gamma0RegionL2 N :=
  (gamma0AllHeightCuspidalMassSpace N).subtypeL.comp
    ((gamma0CuspidalTestCore N h).comp (gamma0CuspidalProjection N))

theorem gamma0CuspidalTestOperator_norm (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (u : Gamma0RegionL2 N) : ‖gamma0CuspidalTestOperator N h u‖≤‖h‖*‖u‖ := by
  change ‖gamma0CuspidalTestCore N h (gamma0CuspidalProjection N u)‖≤_
  exact (spectralHilbertMultiplier_norm _ _ _ _ _ _).trans
    (mul_le_mul_of_nonneg_left (gamma0CuspidalProjection_norm_le N u) (norm_nonneg _))

theorem gamma0CuspidalTestOperator_pair (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (u v : Gamma0RegionL2 N) :
    inner ℂ u (gamma0CuspidalTestOperator N h v)=
      ∑' i : Gamma0AllHeightSpectralIndex N,gamma0CuspidalTestSymbol N h i*
        (inner ℂ u (gamma0FullCuspidalSpectralBasis N i).val*
          inner ℂ (gamma0FullCuspidalSpectralBasis N i).val v) := by
  change inner ℂ u (gamma0CuspidalTestCore N h (gamma0CuspidalProjection N v)).val=_
  rw [← gamma0CuspidalProjection_inner_right,gamma0CuspidalTestCore,spectralHilbertMultiplier_inner]
  apply tsum_congr
  intro i
  rw [gamma0CuspidalProjection_inner_right,gamma0CuspidalProjection_inner_left]

theorem gamma0CuspidalTestOperator_pair_summable (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (u v : Gamma0RegionL2 N) :
    Summable (fun i : Gamma0AllHeightSpectralIndex N => gamma0CuspidalTestSymbol N h i*
      (inner ℂ u (gamma0FullCuspidalSpectralBasis N i).val*
        inner ℂ (gamma0FullCuspidalSpectralBasis N i).val v)) := by
  have hs := spectralHilbertMultiplier_pair_summable (gamma0FullCuspidalSpectralBasis N)
    (gamma0CuspidalTestSymbol N h) ‖h‖ (norm_nonneg _) (gamma0CuspidalTestSymbol_bound N h)
    (gamma0CuspidalProjection N u) (gamma0CuspidalProjection N v)
  simpa only [gamma0CuspidalProjection_inner_right,gamma0CuspidalProjection_inner_left] using hs

theorem gamma0CuspidalTestCore_green (N : ℕ) [NeZero N]
    (u : gamma0AllHeightCuspidalMassSpace N) :
    gamma0CuspidalTestCore N spectralGreenEnergyTest u=gamma0CuspidalGreen N u := by
  let b := gamma0FullCuspidalSpectralBasis N
  apply b.repr.injective
  apply Subtype.ext
  funext i
  rw [gamma0CuspidalTestCore,spectralHilbertMultiplier_repr,gamma0CuspidalTestSymbol_green]
  simp only [b.repr_apply_apply]
  have he : gamma0CuspidalGreen N (b i)=i.1 • b i := by
    apply Subtype.ext
    rw [gamma0CuspidalGreen_apply]
    exact gamma0FullCuspidalSpectralBasis_eigen N i
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (gamma0CuspidalGreen_selfAdjoint N)) (b i) u
  change inner ℂ (gamma0CuspidalGreen N (b i)) u=inner ℂ (b i) (gamma0CuspidalGreen N u) at hs
  rw [he] at hs
  change inner ℂ (i.1 • (b i).val) u.val=inner ℂ (b i).val (gamma0CuspidalGreen N u).val at hs
  rw [inner_smul_left] at hs
  have hc : (starRingEnd ℂ) i.1=i.1 := by
    rw [← gamma0AllHeightSpectralValue_real N i,Complex.conj_ofReal]
  rw [hc] at hs
  change i.1*inner ℂ (b i).val u.val=inner ℂ (b i).val (gamma0CuspidalGreen N u).val
  exact hs

theorem gamma0CuspidalTestOperator_green (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    gamma0CuspidalTestOperator N spectralGreenEnergyTest u=
      gamma0Green N (gamma0CuspidalProjection N u).val := by
  change (gamma0CuspidalTestCore N spectralGreenEnergyTest (gamma0CuspidalProjection N u)).val=_
  rw [gamma0CuspidalTestCore_green,gamma0CuspidalGreen_apply]

end ArtinMatthews
