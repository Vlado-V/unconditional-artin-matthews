module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! # Coordinates -/

namespace OAI.RepresentationTheory.Weil.Local.Coordinates.Construction

noncomputable section

/-! A complete locally compact characteristic-zero normed field is either
ultrametric or admits finite-dimensional real additive coordinates. This is
the part of the local-field dichotomy needed for nonzero Bruhat vectors. -/

open Filter
open scoped _root_.Topology

variable (F : Type) [NormedField F] [CharZero F]

def rationalNorm : AbsoluteValue ℚ ℝ where
  toFun q := ‖(q : F)‖
  map_mul' q r := by simp [norm_mul]
  nonneg' q := norm_nonneg _
  eq_zero' q := by simp
  add_le' q r := by simpa using norm_add_le (q : F) (r : F)

theorem rationalCast_uniformContinuous_of_unbounded
    (h : ¬ ∀ n : ℕ, ‖(n : F)‖ ≤ 1) :
    UniformContinuous (Rat.castHom F : ℚ → F) := by
  have hh : ¬ ∀ n : ℕ, rationalNorm F n ≤ 1 := by
    simpa [rationalNorm] using h
  have he := Rat.AbsoluteValue.equiv_real_of_unbounded hh
  obtain ⟨s, hs, heq⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp he.symm
  have hp (q : ℚ) : ‖(q : F)‖ = ‖q‖ ^ s := by
    have hq := congrFun heq q
    simpa [rationalNorm, Rat.AbsoluteValue.real_eq_abs, ← Real.norm_eq_abs,
      Rat.norm_cast_real] using hq.symm
  apply uniformContinuous_of_continuousAt_zero (Rat.castHom F).toAddMonoidHom
  rw [ContinuousAt, map_zero]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  change Tendsto (fun q : ℚ => ‖(q : F)‖) (𝓝 0) (𝓝 0)
  simp_rw [hp]
  have hc : ContinuousAt (fun q : ℚ => ‖q‖ ^ s) 0 :=
    continuous_norm.continuousAt.rpow_const (Or.inr hs.le)
  simpa [Real.zero_rpow hs.ne'] using hc.tendsto

variable [CompleteSpace F]

def realEmbeddingOfUnbounded (h : ¬ ∀ n : ℕ, ‖(n : F)‖ ≤ 1) : ℝ →+* F :=
  IsDenseInducing.extendRingHom
    (i := Rat.castHom ℝ) (f := Rat.castHom F)
    Rat.isUniformEmbedding_coe_real.isUniformInducing Rat.denseRange_cast
    (rationalCast_uniformContinuous_of_unbounded F h)

theorem realEmbeddingOfUnbounded_continuous
    (h : ¬ ∀ n : ℕ, ‖(n : F)‖ ≤ 1) :
    Continuous (realEmbeddingOfUnbounded F h) :=
  (uniformContinuous_uniformly_extend
    Rat.isUniformEmbedding_coe_real.isUniformInducing Rat.denseRange_cast
    (rationalCast_uniformContinuous_of_unbounded F h)).continuous

theorem exists_real_coordinates_of_unbounded [LocallyCompactSpace F]
    (h : ¬ ∀ n : ℕ, ‖(n : F)‖ ≤ 1) (d : ℕ) :
    ∃ r : ℕ, Nonempty ((Fin r → ℝ) ≃ₜ+ FunctionsMetaplectic.Construction.Position F d) := by
  let : Algebra ℝ F := (realEmbeddingOfUnbounded F h).toAlgebra
  let : ContinuousSMul ℝ F := continuousSMul_of_algebraMap ℝ F
    (realEmbeddingOfUnbounded_continuous F h)
  let : FiniteDimensional ℝ F := FiniteDimensional.of_locallyCompactSpace ℝ
  let b := Module.finBasis ℝ (FunctionsMetaplectic.Construction.Position F d)
  exact ⟨Module.finrank ℝ (FunctionsMetaplectic.Construction.Position F d), ⟨b.equivFunL.symm.toContinuousAddEquiv⟩⟩

end

end OAI.RepresentationTheory.Weil.Local.Coordinates.Construction
