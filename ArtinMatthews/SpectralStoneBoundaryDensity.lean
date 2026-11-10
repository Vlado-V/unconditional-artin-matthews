module

public import ArtinMatthews.SpectralStoneRegularEnergies
public import ArtinMatthews.SpectralCompactResolventBoundary
public import ArtinMatthews.SpectralEisensteinMeromorphicTests
public import ArtinMatthews.SpectralCompactResolventCriticalJump
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

/-! The actual upper resolvent boundary supplies the continuous density
at all regular energies. It is zero below the continuous threshold. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0StoneBoundaryDensity (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (x : ℝ) : ℝ :=
  (gamma0CompactForcingDiagonalTest N ψ Y (spectralStoneUpperParameter x 0)).im/Real.pi

theorem gamma0StoneBoundaryDensity_continuousOn (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) :
    ContinuousOn (gamma0StoneBoundaryDensity N ψ Y) (gamma0StoneGoodEnergy N ψ Y) := by
  intro x hx
  have hu : gamma0HeightMatchingRegular N Y.height Y.pos (spectralStoneUpperParameter x 0) := hx.2.1
  have h : ContinuousAt (fun x : ℝ =>
      gamma0CompactForcingDiagonalTest N ψ Y (spectralStoneUpperParameter x 0)) x :=
    (gamma0CompactForcingDiagonalTest_analyticAt_regular N ψ Y _ hu).continuousAt.comp
      (f:=fun x : ℝ => spectralStoneUpperParameter x 0)
      spectralStoneUpperParameter_boundary_continuous.continuousAt
  exact ((Complex.continuous_im.continuousAt.comp h).div_const Real.pi).continuousWithinAt

theorem gamma0StoneBoundaryDensity_subcritical (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) (x : ℝ)
    (hx : x∈gamma0StoneGoodEnergy N ψ Y) (hx₀ : x<1/4) :
    gamma0StoneBoundaryDensity N ψ Y x=0 := by
  have hc := congrArg Complex.im (gamma0CompactForcingStone_boundary_conj N ψ Y x hx.2.1 hx.2.2.1)
  rw [spectralStoneLowerParameter_subcritical x hx₀.le,Complex.conj_im] at hc
  have h : (gamma0CompactForcingDiagonalTest N ψ Y (spectralStoneUpperParameter x 0)).im=0 := by
    linarith
  rw [gamma0StoneBoundaryDensity,h,zero_div]

theorem gamma0StoneBoundaryDensity_supercritical (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) (x : ℝ)
    (hx : x∈gamma0StoneGoodEnergy N ψ Y) (hx₀ : (1/4:ℝ)<x) :
    gamma0StoneBoundaryDensity N ψ Y x=
      (∑ i,‖gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i)
        ψ (eisensteinCriticalPoint (Real.sqrt (x-1/4)))‖^2)/(4*Real.pi*Real.sqrt (x-1/4)) := by
  let t := Real.sqrt (x-1/4)
  let s := spectralStoneLowerParameter x 0
  let q := spectralStoneUpperParameter x 0
  have ht : 0<t := Real.sqrt_pos.mpr (sub_pos.mpr hx₀)
  have hS : s=eisensteinCriticalPoint t := spectralStoneLowerParameter_critical x hx₀.le
  have hQ : q=1-s := (spectralStoneUpperParameter_critical x hx₀.le).trans
    (congrArg (fun z : ℂ => 1-z) hS.symm)
  have hs : s.re=1/2 := by rw [hS,eisensteinCriticalPoint_re]
  have hti : s.im=t := by rw [hS,eisensteinCriticalPoint_im]
  have hq : gamma0HeightMatchingRegular N Y.height Y.pos (1-s) := by
    rw [← hQ]
    exact hx.2.1
  have hj := gamma0CompactForcingResolvent_critical_jump_im N ψ Y s hs
    (by simpa only [hti] using ht.ne') hx.2.2.2 hx.2.2.1 hq
  let S : ℝ := ∑ i,‖gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i) ψ s‖^2
  let M := gamma0CompactForcingDiagonalTest N ψ Y
  change (M s-M (1-s)).im= -(S/(2*s.im)) at hj
  rw [Complex.sub_im,← hQ,hti] at hj
  have hc := congrArg Complex.im (gamma0CompactForcingStone_boundary_conj N ψ Y x hx.2.1 hx.2.2.1)
  change ((starRingEnd ℂ) (M s)).im=(M q).im at hc
  rw [Complex.conj_im] at hc
  have hd : S/(2*t)=2*(S/(4*t)) := by field_simp [ht.ne']; ring
  have hi : (M q).im=S/(4*t) := by linarith
  change (M q).im/Real.pi=
    (∑ i,‖gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i)
      ψ (eisensteinCriticalPoint t)‖^2)/(4*Real.pi*t)
  rw [hi,← hS]
  change (S/(4*t))/Real.pi=S/(4*Real.pi*t)
  ring

theorem gamma0StoneBoundaryDensity_nonneg (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) (x : ℝ)
    (hx : x∈gamma0StoneGoodEnergy N ψ Y) :
    0 ≤ gamma0StoneBoundaryDensity N ψ Y x := by
  rcases lt_or_gt_of_ne hx.1 with h | h
  · rw [gamma0StoneBoundaryDensity_subcritical N ψ Y x hx h]
  · rw [gamma0StoneBoundaryDensity_supercritical N ψ Y x hx h]
    positivity

end ArtinMatthews
