module

public import ArtinMatthews.SourceJacquetHaar
public import ArtinMatthews.StandardAdelicLocalNontrivial
public import ArtinMatthews.StandardLocalFourier
public import ArtinMatthews.SourceLocalAdditiveModulus
public import ArtinMatthews.StandardLocalHaarScaling
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

/-! The volume-one Haar of the literal Jacquet calculation is the
actual standard self-dual Haar at an exterior place. Dilation of a
set integral has the exact normalized finite-place modulus. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical Set
open scoped NumberField SourcePhysical Pointwise ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

theorem sourceJacquetHaar_eq_selfDual (hP : P ∉ traceBadPlaces K) :
    sourceJacquetHaar K P = sourceLocalSelfDual K P := by
  let : (sourceJacquetHaar K P).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  refine sourceLocalSelfDual_eq_of_good_volume K P _ hP ?_
  rw [sourceLocalBall_zero_eq_integerOpen]
  exact sourceJacquetHaar_integers K P

theorem sourceJacquetSetIntegral_dilation {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hP : P ∉ traceBadPlaces K) (t : (P.adicCompletion K)ˣ) (s : Set (P.adicCompletion K))
    (f : P.adicCompletion K → V) :
    (∫ x in (fun x => (t : P.adicCompletion K) * x) '' s, f x ∂(sourceJacquetHaar K P)) =
      ‖(t : P.adicCompletion K)‖ •
        ∫ x in s, f ((t : P.adicCompletion K) * x) ∂(sourceJacquetHaar K P) := by
  let L := P.adicCompletion K
  let μ := sourceJacquetHaar K P
  let e := MeasurableEquiv.mulLeft₀ ((t⁻¹ : Lˣ) : L) t⁻¹.ne_zero
  have he : μ.map e = (‖(t : L)‖₊ : ℝ≥0∞) • μ := by
    change μ.map (fun x : L => ((t⁻¹ : Lˣ) : L) * x) = _
    rw [show μ = sourceLocalSelfDual K P from sourceJacquetHaar_eq_selfDual K P hP,
      sourceLocalSelfDual_map_mul K P t⁻¹, inv_inv]
  have hs : e ⁻¹' s = (fun x : L => (t : L) * x) '' s := by
    change (fun x : L => t⁻¹ • x) ⁻¹' s = t • s
    exact preimage_smul_inv t s
  have hf : (fun x => f ((t : L) * e x)) = f := by
    funext x
    apply congrArg f
    change (t : L) * (((t⁻¹ : Lˣ) : L) * x) = x
    rw [Units.val_inv_eq_inv_val, ← mul_assoc, mul_inv_cancel₀ t.ne_zero, one_mul]
  have h := setIntegral_map_equiv (μ := μ) e (fun x => f ((t : L) * x)) s
  rw [he, hs, hf, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal] at h
  exact h.symm

end
end ArtinMatthews
