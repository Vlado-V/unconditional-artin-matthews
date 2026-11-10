module

public import ArtinMatthews.SpectralModularWeakFunctionals
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Separation by actual scalar coordinates of the finite modular-chart L²
gradient, and the resulting faithful mass criterion for the energy graph. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem modularGradient_eq_zero_of_components
    (f : Lp (EuclideanSpace ℂ (Fin 2)) 2 (volume.restrict ModularGroup.fd))
    (hf : ∀ i : Fin 2, modularGradientComponent i f = 0) : f = 0 := by
  have hcoord (i : Fin 2) : ∀ᵐ z ∂volume.restrict ModularGroup.fd, f z i = 0 := by
    have hc := modularGradientComponent_ae i f
    rw [hf i] at hc
    filter_upwards [hc,Lp.coeFn_zero ℂ 2 (volume.restrict ModularGroup.fd)] with z hz hzero
    exact hz.symm.trans hzero
  have hall : ∀ᵐ z ∂volume.restrict ModularGroup.fd, ∀ i : Fin 2, f z i = 0 :=
    ae_all_iff.mpr hcoord
  apply Lp.ext
  filter_upwards [hall,Lp.coeFn_zero (EuclideanSpace ℂ (Fin 2)) 2
    (volume.restrict ModularGroup.fd)] with z hz hzero
  rw [hzero]
  apply PiLp.ext
  intro i
  exact hz i

theorem gamma0EnergyGradient_eq_zero_of_charts (N : ℕ) [NeZero N]
    (u : gamma0EnergySpace N)
    (hu : ∀ (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (i : Fin 2),
      gamma0EnergyGradientChart N q i u = 0) : gamma0EnergyGradient N u = 0 := by
  apply PiLp.ext
  intro q
  apply modularGradient_eq_zero_of_components
  intro i
  exact hu q i

theorem gamma0Energy_eq_zero_of_mass_gradient_zero (N : ℕ) [NeZero N]
    (u : gamma0EnergySpace N) (hm : gamma0EnergyInclusion N u = 0)
    (hg : gamma0EnergyGradient N u = 0) : u = 0 := by
  have h := gamma0Energy_norm_sq N u
  simp only [hm,hg,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_add] at h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)

end ArtinMatthews
