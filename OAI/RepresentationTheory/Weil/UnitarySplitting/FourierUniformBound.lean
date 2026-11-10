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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierUltra


set_option backward.privateInPublic true
@[expose] public section

/-! # Fourier Uniform Bound -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.FourierUniformBound.Construction

noncomputable section

/-! A uniform translation radius gives a uniform bound on Fourier support. -/

open _root_.MeasureTheory

theorem fourier_support_bound_of_translation
    {F : Type} [NormedField F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] {d : ℕ}
    (ψ : AddChar F ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [μ.IsAddHaarMeasure]
    (a : F) (ha : ψ a ≠ 1) (ε : ℝ) (hε : 0 < ε)
    (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) (ht : ∀ x t, ‖t‖ < ε → f (x + t) = f x)
    (x : Local.FunctionsMetaplectic.Construction.Position F d) (hx : Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x ≠ 0) : ‖x‖ ≤ ‖a‖ / ε := by
  have hR : 0 ≤ ‖a‖ / ε := div_nonneg (norm_nonneg _) hε.le
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  by_contra! hi
  have hxi : x i ≠ 0 := norm_pos_iff.mp (hR.trans_lt hi)
  let t : Local.FunctionsMetaplectic.Construction.Position F d := Pi.single i (a / x i)
  have htn : ‖t‖ < ε := by
    rw [show ‖t‖ = ‖a / x i‖ from Pi.norm_single _, norm_div]
    apply (div_lt_iff₀ (norm_pos_iff.mpr hxi)).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hi
  have hdot : Local.FunctionsMetaplectic.Construction.dot x t = a := by
    simp only [Local.FunctionsMetaplectic.Construction.dot, t, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    field_simp
  exact hx (FourierUltra.Construction.fourierIntegral_vanishes_of_translation ψ μ f t x
    (fun y => ht y t htn) (by rwa [hdot]))

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.FourierUniformBound.Construction
