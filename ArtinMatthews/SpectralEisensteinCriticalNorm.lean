module

public import ArtinMatthews.SpectralEisensteinCriticalEnergy
public import ArtinMatthews.SpectralEisensteinCriticalCuspFlux
public import ArtinMatthews.SpectralEisensteinCriticalPowerFlux
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

/-! Real energy makes the total imaginary upper flux vanish. The actual
critical-line scattering matrix preserves the finite cusp norm at every
regular point away from the zero-frequency threshold. -/
noncomputable section
open Set Matrix
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem spectralComplexHilbert_self_im_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : E) : (inner ℂ u u).im=0 := by
  have he : inner ℂ u u=((‖u‖^2:ℝ):ℂ) := by
    rw [Complex.ofReal_pow]
    exact inner_self_eq_norm_sq_to_K u
  rw [he,Complex.ofReal_im]

theorem gamma0EisensteinCriticalTopForcing_flux_zero (N : ℕ) [NeZero N]
    (s : ℂ) (hs : s.re=1/2) (hreg : gamma0EisensteinMatchingRegular N s)
    (c : Gamma0EisensteinCuspClasses N → ℂ) :
    (inner ℂ (gamma0EisensteinCriticalTopForcing N s c)
      (gamma0EnergyInclusion N (gamma0EisensteinCriticalTruncatedEnergy N s c))).im=0 := by
  let u := gamma0EisensteinCriticalTruncatedEnergy N s c
  let F := gamma0EisensteinCriticalTopForcing N s c
  let ζ := s*(1-s)
  have hζ : ζ.im=0 := eisensteinCriticalParameter_real hs
  have hP : (inner ℂ u (gamma0EnergyResolventPencil N ζ u)).im=0 := by
    rw [gamma0EnergyResolventPencil_inner]
    simp only [Complex.sub_im,Complex.mul_im,spectralComplexHilbert_self_im_zero,hζ,
      mul_zero,zero_mul,add_zero,sub_zero]
  have he : (inner ℂ u (gamma0EnergyResolventPencil N ζ u)).im=
      (inner ℂ u (gamma0EnergyMassAdjoint N (-F))).im :=
    congrArg (fun v : gamma0EnergySpace N => (inner ℂ u v).im)
      (gamma0EisensteinCriticalTruncatedEnergy_pencil N s hreg c)
  rw [hP,gamma0EnergyMassAdjoint_inner,inner_neg_right (𝕜 := ℂ) (E := Gamma0RegionL2 N),
    ← inner_conj_symm (𝕜 := ℂ) (gamma0EnergyInclusion N u) F,Complex.neg_im,Complex.conj_im,neg_neg] at he
  exact he.symm

theorem gamma0CuspScatteringMatrix_norm_sq_regular (N : ℕ) [NeZero N]
    (s : ℂ) (hs : s.re=1/2) (ht : s.im≠0) (hreg : gamma0EisensteinMatchingRegular N s)
    (c : Gamma0EisensteinCuspClasses N → ℂ) :
    (∑ i,‖(gamma0CuspScatteringMatrix N s).mulVec c i‖^2)=∑ i,‖c i‖^2 := by
  have h := gamma0EisensteinCriticalTopForcing_flux_zero N s hs hreg c
  rw [gamma0EisensteinCriticalTopForcing_sum_pair,sum_inner,Complex.im_sum] at h
  simp only [gamma0EisensteinCriticalTopPairMass_inner_flux N s hs c,← Finset.mul_sum,
    Finset.sum_sub_distrib] at h
  exact (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left ht)).symm

end ArtinMatthews
