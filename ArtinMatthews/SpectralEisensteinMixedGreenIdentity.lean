module

public import ArtinMatthews.SpectralEisensteinMixedUpperEnergy
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

/-! The actual full energy pencil at real energy gives the mixed
Green identity for the compact forced and Eisenstein truncations. -/
noncomputable section
open Matrix
open scoped InnerProductSpace MatrixGroups
namespace ArtinMatthews

theorem gamma0EnergyMassAdjoint_inner_left (N : ℕ) [NeZero N] (F : Gamma0RegionL2 N)
    (v : gamma0EnergySpace N) :
    inner ℂ (gamma0EnergyMassAdjoint N F) v=inner ℂ F (gamma0EnergyInclusion N v) := by
  rw [gamma0EnergyMassAdjoint, ContinuousLinearMap.adjoint_inner_left]

theorem gamma0EnergyResolventPencil_inner_left_eq_real (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.im=0) (u v : gamma0EnergySpace N) :
    inner ℂ (gamma0EnergyResolventPencil N z u) v=inner ℂ u (gamma0EnergyResolventPencil N z v) := by
  have hReal : (starRingEnd ℂ) z=z := by
    apply Complex.ext
    · simp
    · simp [hz]
  let P := gamma0EnergyResolventPencil N z
  let J := gamma0EnergyInclusion N
  let G := gamma0EnergyGradient N
  have hGrad : (starRingEnd ℂ) (inner ℂ (G v) (G u))=inner ℂ (G u) (G v) :=
    inner_conj_symm (𝕜:=ℂ) (G u) (G v)
  have hMass : (starRingEnd ℂ) (inner ℂ (J v) (J u))=inner ℂ (J u) (J v) :=
    inner_conj_symm (𝕜:=ℂ) (J u) (J v)
  change inner ℂ (P u) v=inner ℂ u (P v)
  calc
    _ = (starRingEnd ℂ) (inner ℂ v (P u)) :=
      (inner_conj_symm (𝕜:=ℂ) (P u) v).symm
    _ = (starRingEnd ℂ) (inner ℂ (G v) (G u)-z*inner ℂ (J v) (J u)) :=
      congrArg (starRingEnd ℂ) (gamma0EnergyResolventPencil_inner N z v u)
    _ = inner ℂ (G u) (G v)-z*inner ℂ (J u) (J v) := by
      rw [map_sub,map_mul,hGrad,hMass,hReal]
    _ = _ := (gamma0EnergyResolventPencil_inner N z u v).symm

theorem gamma0CompactEisenstein_mixed_green (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s.re=1/2) (hr : gamma0EisensteinMatchingRegular N s)
    (hq : gamma0HeightMatchingRegular N Y.height Y.pos (1-s))
    (A : ℝ) (hA : 0<A) (hA2 : A≤1/2) (c : Gamma0EisensteinCuspClasses N → ℂ) :
    let U := gamma0CompactForcingUpperEnergy N ψ Y (1-s) A hA
    let V := gamma0EisensteinUpperCombination N s A hA c
    let J := gamma0EnergyInclusion N
    inner ℂ (gamma0SmoothSeedMass N ψ) (J V)=
      inner ℂ (gamma0CompactForcingUpperForce N ψ Y (1-s) A hA) (J V)-
        inner ℂ (J U) (gamma0EisensteinUpperForceCombination N s A hA c) := by
  dsimp only
  let U := gamma0CompactForcingUpperEnergy N ψ Y (1-s) A hA
  let V := gamma0EisensteinUpperCombination N s A hA c
  have h := gamma0EnergyResolventPencil_inner_left_eq_real N (s*(1-s))
    (eisensteinCriticalParameter_real hs) U V
  have hU := gamma0CompactForcingUpperEnergy_pencil N ψ Y (1-s) hq A hA hA2
  rw [gamma0Eisenstein_reflect_parameter] at hU
  change gamma0EnergyResolventPencil N (s*(1-s)) U=
    gamma0EnergyMassAdjoint N (gamma0SmoothSeedMass N ψ-gamma0CompactForcingUpperForce N ψ Y (1-s) A hA) at hU
  have hV : gamma0EnergyResolventPencil N (s*(1-s)) V=
      gamma0EnergyMassAdjoint N (-gamma0EisensteinUpperForceCombination N s A hA c) :=
    gamma0EisensteinUpperCombination_pencil N s hr A hA hA2 c
  rw [hU,hV,gamma0EnergyMassAdjoint_inner_left,gamma0EnergyMassAdjoint_inner,
    inner_sub_left (𝕜:=ℂ) (E:=Gamma0RegionL2 N),inner_neg_right (𝕜:=ℂ) (E:=Gamma0RegionL2 N)] at h
  linear_combination h

end ArtinMatthews
