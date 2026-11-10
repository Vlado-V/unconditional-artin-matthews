module

public import ArtinMatthews.SpectralSectionWeakPairing
public import Mathlib.NumberTheory.Modular
public import ArtinMatthews.SpectralPoincareL2
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

/-! Actual compact weak-test coefficients and their L² representatives on
modular charts. Integrability is derived from compact support and the proved
finite area of the modular region. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

def spectralWeakValueTest (φ : ℝ × ℝ → ℂ) (i : Fin 2) (p : ℝ × ℝ) : ℂ :=
  p.2^2 • fderiv ℝ φ p (spectralPlaneDirection i)

def spectralWeakGradientTest (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := p.2 • φ p

def modularPlaneTest (r : SL(2, ℤ)) (φ : ℝ × ℝ → ℂ) (z : UpperHalfPlane) : ℂ :=
  φ ((r⁻¹ • z).re,(r⁻¹ • z).im)

theorem modularPlaneTest_memLp (r : SL(2, ℤ)) (φ : ℝ × ℝ → ℂ)
    (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    MemLp (modularPlaneTest r φ) 2 (volume.restrict ModularGroup.fd) := by
  obtain ⟨C,hC⟩ := (hs.isCompact_range hφ).isBounded.exists_norm_le
  have hact : Continuous (fun z : UpperHalfPlane => r⁻¹ • z) := by
    change Continuous (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹ • z)
    exact continuous_const_smul _
  have hm : Continuous (modularPlaneTest r φ) :=
    hφ.comp ((UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im).comp hact)
  apply MemLp.of_bound hm.aestronglyMeasurable C
  exact Eventually.of_forall (fun z => hC _ ⟨_,rfl⟩)

theorem spectralWeakValueTest_continuous (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (i : Fin 2) : Continuous (spectralWeakValueTest φ i) :=
  (continuous_snd.pow 2).smul
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)

theorem spectralWeakValueTest_compact (φ : ℝ × ℝ → ℂ)
    (hs : HasCompactSupport φ) (i : Fin 2) : HasCompactSupport (spectralWeakValueTest φ i) := by
  apply (hs.fderiv_apply ℝ (spectralPlaneDirection i)).mono'
  intro p hp
  by_contra hout
  have hz : fderiv ℝ φ p (spectralPlaneDirection i) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun q => fderiv ℝ φ q (spectralPlaneDirection i)) hout
  exact hp (by simp only [spectralWeakValueTest,hz,smul_zero])

theorem spectralWeakGradientTest_continuous (φ : ℝ × ℝ → ℂ)
    (hφ : Continuous φ) : Continuous (spectralWeakGradientTest φ) := continuous_snd.smul hφ

theorem spectralWeakGradientTest_compact (φ : ℝ × ℝ → ℂ)
    (hs : HasCompactSupport φ) : HasCompactSupport (spectralWeakGradientTest φ) := by
  apply hs.mono'
  intro p hp
  by_contra hout
  have hz : φ p = 0 := image_eq_zero_of_notMem_tsupport hout
  exact hp (by simp only [spectralWeakGradientTest,hz,smul_zero])

theorem modularWeakValueTest_memLp (r : SL(2, ℤ)) (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (i : Fin 2) :
    MemLp (modularPlaneTest r (spectralWeakValueTest φ i)) 2
      (volume.restrict ModularGroup.fd) :=
  modularPlaneTest_memLp r _ (spectralWeakValueTest_continuous φ hφ i)
    (spectralWeakValueTest_compact φ hs i)

theorem modularWeakGradientTest_memLp (r : SL(2, ℤ)) (φ : ℝ × ℝ → ℂ)
    (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    MemLp (modularPlaneTest r (spectralWeakGradientTest φ)) 2
      (volume.restrict ModularGroup.fd) :=
  modularPlaneTest_memLp r _ (spectralWeakGradientTest_continuous φ hφ)
    (spectralWeakGradientTest_compact φ hs)

end ArtinMatthews
