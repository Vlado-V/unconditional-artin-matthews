module

public import ArtinMatthews.SpectralGamma0EnergyGraph
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.L2Space
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

/-! Actual bounded L² weak-test functionals and literal chart representatives
of the completed value and gradient maps. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace

namespace ArtinMatthews

def modularL2Pairing (t : UpperHalfPlane → ℂ)
    (ht : MemLp t 2 (volume.restrict ModularGroup.fd)) :
    Lp ℂ 2 (volume.restrict ModularGroup.fd) →L[ℂ] ℂ :=
  innerSL ℂ (ht.star.toLp (star t))

theorem modularL2Pairing_apply (t : UpperHalfPlane → ℂ)
    (ht : MemLp t 2 (volume.restrict ModularGroup.fd))
    (f : Lp ℂ 2 (volume.restrict ModularGroup.fd)) :
    modularL2Pairing t ht f = ∫ z in ModularGroup.fd, f z*t z := by
  change inner ℂ (ht.star.toLp (star t)) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ht.star.coeFn_toLp] with z hz
  rw [hz]
  simp only [RCLike.inner_apply,Pi.star_apply,starRingEnd_apply,star_star]

def spectralFrameCoordinate (i : Fin 2) : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ :=
  PiLp.proj 2 (fun _ : Fin 2 => ℂ) i

theorem spectralFrameCoordinate_apply (i : Fin 2) (v : EuclideanSpace ℂ (Fin 2)) :
    spectralFrameCoordinate i v = v i := rfl

def modularGradientComponent (i : Fin 2) :
    Lp (EuclideanSpace ℂ (Fin 2)) 2 (volume.restrict ModularGroup.fd) →L[ℂ]
      Lp ℂ 2 (volume.restrict ModularGroup.fd) :=
  (spectralFrameCoordinate i).compLpL 2 (volume.restrict ModularGroup.fd)

theorem modularGradientComponent_ae (i : Fin 2)
    (f : Lp (EuclideanSpace ℂ (Fin 2)) 2 (volume.restrict ModularGroup.fd)) :
    (modularGradientComponent i f : UpperHalfPlane → ℂ) =ᵐ[volume.restrict ModularGroup.fd]
      (fun z => f z i) :=
  (spectralFrameCoordinate i).coeFn_compLpL f

def gamma0EnergyMassChart (N : ℕ) [NeZero N]
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    gamma0EnergySpace N →L[ℂ] Lp ℂ 2 (volume.restrict ModularGroup.fd) :=
  (PiLp.proj 2 (fun _ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
    Lp ℂ 2 (volume.restrict ModularGroup.fd)) q).comp (gamma0EnergyInclusion N)

def gamma0EnergyGradientChart (N : ℕ) [NeZero N]
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (i : Fin 2) :
    gamma0EnergySpace N →L[ℂ] Lp ℂ 2 (volume.restrict ModularGroup.fd) :=
  (modularGradientComponent i).comp
    ((PiLp.proj 2 (fun _ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
      Lp (EuclideanSpace ℂ (Fin 2)) 2 (volume.restrict ModularGroup.fd)) q).comp
        (gamma0EnergyGradient N))

theorem gamma0EnergyMassChart_test_ae (N : ℕ) [NeZero N]
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (ψ : h2SmoothCompactSeeds) :
    (gamma0EnergyMassChart N q (gamma0EnergyTest N ψ) : UpperHalfPlane → ℂ)
      =ᵐ[volume.restrict ModularGroup.fd]
        (fun z => gamma0PoincareSeed N ψ.val (q.out⁻¹ • z)) :=
  gamma0SeedMass_coeFn N ψ.val q

theorem gamma0EnergyGradientChart_test_ae (N : ℕ) [NeZero N]
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (i : Fin 2)
    (ψ : h2SmoothCompactSeeds) :
    (gamma0EnergyGradientChart N q i (gamma0EnergyTest N ψ) : UpperHalfPlane → ℂ)
      =ᵐ[volume.restrict ModularGroup.fd]
        (fun z => h2SectionGradient (gamma0PoincareSeed N ψ.val) (q.out⁻¹ • z) i) := by
  have hc := modularGradientComponent_ae i ((gamma0SeedGradient N ψ) q)
  have hg := arithmeticPoincareGradientRegionLp_coeFn
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ψ
    (Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹)
  filter_upwards [hc,hg] with z hz hzg
  change (modularGradientComponent i ((gamma0SeedGradient N ψ) q)) z = _
  rw [hz]
  change (arithmeticPoincareGradientRegionLp _ ψ
    (Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹) z) i = _
  rw [hzg]
  rfl

end ArtinMatthews
