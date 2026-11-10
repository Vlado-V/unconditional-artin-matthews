module

public import ArtinMatthews.SourceJacquetHaar
public import ArtinMatthews.StandardAdelicLocalNontrivial
public import ArtinMatthews.SourceJacquetHaarDilation
public import ArtinMatthews.SourceLocalAdditiveModulus
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

/-! Genuine integrability is preserved by the change of variables on
local Jacquet balls. The Haar modulus is finite and strictly positive. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField SourcePhysical ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

theorem sourceJacquetIntegrableOn_dilation_iff {V : Type*} [NormedAddCommGroup V]
    (hP : P ∉ traceBadPlaces K) (t : (P.adicCompletion K)ˣ) (s : Set (P.adicCompletion K))
    (f : P.adicCompletion K → V) :
    IntegrableOn f ((fun x => (t : P.adicCompletion K) * x) '' s) (sourceJacquetHaar K P) ↔
      IntegrableOn (fun x => f ((t : P.adicCompletion K) * x)) s (sourceJacquetHaar K P) := by
  let L := P.adicCompletion K
  let μ := sourceJacquetHaar K P
  let e := MeasurableEquiv.mulLeft₀ (t : L) t.ne_zero
  let c : ℝ≥0∞ := ‖((t⁻¹ : Lˣ) : L)‖₊
  have he : μ.map e = c • μ := by
    change μ.map (fun x : L => (t : L) * x) = _
    rw [show μ = sourceLocalSelfDual K P from sourceJacquetHaar_eq_selfDual K P hP, sourceLocalSelfDual_map_mul]
  have h0 : c ≠ 0 := by simp [c]
  have ht : c ≠ ∞ := ENNReal.coe_ne_top
  have hr : (μ.map e).restrict (e '' s) = (μ.restrict s).map e := by
    rw [e.measurableEmbedding.restrict_map, Set.preimage_image_eq _ e.injective]
  change Integrable f (μ.restrict (e '' s)) ↔ Integrable (fun x => f (e x)) (μ.restrict s)
  calc
    _ ↔ Integrable f ((c • μ).restrict (e '' s)) := by
      rw [Measure.restrict_smul, integrable_smul_measure h0 ht]
    _ ↔ _ := by
      rw [← he, hr, e.measurableEmbedding.integrable_map_iff]
      rfl

end
end ArtinMatthews
