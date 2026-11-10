module

public import ArtinMatthews.SpectralKLWeightedMeasures
public import ArtinMatthews.SpectralKLPositiveSmoothDensity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Order.CompletePartialOrder
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

/-! The actual dense vector space of smooth compact positive spectral
tests, mapped into the literal weighted L2 space. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ArtinMatthews

def spectralKLTestSubmodule : Submodule ℂ (ℝ → ℂ) where
  carrier := {g | ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ioi (0 : ℝ)}
  zero_mem' := ⟨contDiff_const,HasCompactSupport.zero,by simp⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1,hf.2.1.add hg.2.1,(tsupport_add f g).trans (union_subset hf.2.2 hg.2.2)⟩
  smul_mem' := by
    intro c f hf
    exact ⟨contDiff_const.smul hf.1,hf.2.1.smul_left,(tsupport_smul_subset_right (fun _ : ℝ => c) f).trans hf.2.2⟩

def spectralKLTestToLp : spectralKLTestSubmodule →ₗ[ℂ] Lp ℂ 2 spectralKLSpectralMeasure where
  toFun g := (spectralKLSpectralMeasure_memLp_compact g g.property.1.continuous g.property.2.1).toLp g
  map_add' f g := by
    exact MemLp.toLp_add
      (spectralKLSpectralMeasure_memLp_compact f f.property.1.continuous f.property.2.1)
      (spectralKLSpectralMeasure_memLp_compact g g.property.1.continuous g.property.2.1)
  map_smul' c g := by
    exact MemLp.toLp_const_smul c
      (spectralKLSpectralMeasure_memLp_compact g g.property.1.continuous g.property.2.1)

theorem spectralKLTestToLp_coe (g : spectralKLTestSubmodule) :
    spectralKLTestToLp g =ᵐ[spectralKLSpectralMeasure] (g : ℝ → ℂ) :=
  MemLp.coeFn_toLp (spectralKLSpectralMeasure_memLp_compact g g.property.1.continuous g.property.2.1)

theorem spectralKLTestToLp_denseRange : DenseRange spectralKLTestToLp := by
  apply spectralKLSpectralMeasure_dense_positive_smooth.mono
  intro u hu
  obtain ⟨g,hug,hgc,hg,hgp⟩ := hu
  let v : spectralKLTestSubmodule := ⟨g,⟨hg,hgc,hgp⟩⟩
  refine ⟨v,?_⟩
  apply Lp.ext
  exact (spectralKLTestToLp_coe v).trans hug.symm

end ArtinMatthews
