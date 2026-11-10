module

public import ArtinMatthews.SpectralStoneEisensteinPair
public import ArtinMatthews.SpectralEisensteinCriticalTests
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

/-! The actual compact Eisenstein coefficient as an element of its
normalized positive-frequency L² space. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0EisensteinSpectralMeasure : Measure ℝ :=
  ENNReal.ofReal ((2*Real.pi)⁻¹) • volume.restrict (Ioi 0)

theorem gamma0EisensteinCoefficient_memLp (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (ψ : h2SmoothCompactSeeds) :
    MemLp (fun t => (starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ψ i t)) 2
      gamma0EisensteinSpectralMeasure := by
  have ha : AEStronglyMeasurable (fun t => (starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ψ i t))
      (volume.restrict (Ioi 0)) :=
    (Complex.continuous_conj.measurable.comp (gamma0StoneEisensteinAmplitude_measurable N ψ i)).aestronglyMeasurable
  have hi : IntegrableOn (fun t => ‖(starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ψ i t)‖^2) (Ioi 0) := by
    simpa only [Complex.norm_conj] using gamma0StoneEisensteinAmplitude_sq_integrableOn N ψ i
  exact ((memLp_two_iff_integrable_sq_norm ha).mpr hi).smul_measure ENNReal.ofReal_ne_top

def gamma0EisensteinCoefficientLp (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (ψ : h2SmoothCompactSeeds) :
    Lp ℂ 2 gamma0EisensteinSpectralMeasure :=
  (gamma0EisensteinCoefficient_memLp N i ψ).toLp _

theorem gamma0EisensteinCoefficientLp_ae (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (ψ : h2SmoothCompactSeeds) :
    gamma0EisensteinCoefficientLp N i ψ=ᵐ[gamma0EisensteinSpectralMeasure]
      fun t => (starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ψ i t) :=
  (gamma0EisensteinCoefficient_memLp N i ψ).coeFn_toLp

theorem gamma0EisensteinCoefficientLp_add (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (ψ ξ : h2SmoothCompactSeeds) :
    gamma0EisensteinCoefficientLp N i (ψ+ξ)=gamma0EisensteinCoefficientLp N i ψ+gamma0EisensteinCoefficientLp N i ξ := by
  apply Lp.ext
  filter_upwards [gamma0EisensteinCoefficientLp_ae N i (ψ+ξ),gamma0EisensteinCoefficientLp_ae N i ψ,
    gamma0EisensteinCoefficientLp_ae N i ξ,Lp.coeFn_add (gamma0EisensteinCoefficientLp N i ψ)
      (gamma0EisensteinCoefficientLp N i ξ)] with t hsum hψ hξ hadd
  rw [hsum,hadd]
  simp only [Pi.add_apply]
  rw [hψ,hξ]
  change (starRingEnd ℂ) (gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i)
      (ψ+ξ) (eisensteinCriticalPoint t))=_
  rw [gamma0CuspEisensteinMeromorphicTest_add_seed,map_add]
  rfl

theorem gamma0EisensteinCoefficientLp_smul (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (c : ℂ) (ψ : h2SmoothCompactSeeds) :
    gamma0EisensteinCoefficientLp N i (c • ψ)=c • gamma0EisensteinCoefficientLp N i ψ := by
  apply Lp.ext
  filter_upwards [gamma0EisensteinCoefficientLp_ae N i (c • ψ),gamma0EisensteinCoefficientLp_ae N i ψ,
    Lp.coeFn_smul c (gamma0EisensteinCoefficientLp N i ψ)] with t hsum hψ hsmul
  rw [hsum,hsmul]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hψ]
  change (starRingEnd ℂ) (gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i)
      (c • ψ) (eisensteinCriticalPoint t))=_
  rw [gamma0CuspEisensteinMeromorphicTest_smul_seed,map_mul,
    show (starRingEnd ℂ) ((starRingEnd ℂ) c)=c from star_star c]
  rfl

def gamma0EisensteinCoefficientLinear (N : ℕ) [NeZero N] (i : Gamma0EisensteinCuspClasses N) :
    h2SmoothCompactSeeds →ₗ[ℂ] Lp ℂ 2 gamma0EisensteinSpectralMeasure where
  toFun := gamma0EisensteinCoefficientLp N i
  map_add' := gamma0EisensteinCoefficientLp_add N i
  map_smul' := gamma0EisensteinCoefficientLp_smul N i

theorem gamma0EisensteinCoefficientLp_norm_sq (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (ψ : h2SmoothCompactSeeds) :
    ‖gamma0EisensteinCoefficientLp N i ψ‖^2=
      (2*Real.pi)⁻¹*(∫ t in Ioi 0,‖gamma0StoneEisensteinAmplitude N ψ i t‖^2) := by
  calc
    _ = ∫ t,‖gamma0EisensteinCoefficientLp N i ψ t‖^2 ∂gamma0EisensteinSpectralMeasure := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    _ = ∫ t,‖(starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ψ i t)‖^2 ∂gamma0EisensteinSpectralMeasure :=
      integral_congr_ae ((gamma0EisensteinCoefficientLp_ae N i ψ).mono fun t ht => congrArg (fun z : ℂ => ‖z‖^2) ht)
    _ = _ := by
      have hp : 0≤(2*Real.pi)⁻¹ := inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le)
      simp only [Complex.norm_conj,gamma0EisensteinSpectralMeasure,integral_smul_measure,
        ENNReal.toReal_ofReal hp,smul_eq_mul]

end ArtinMatthews
