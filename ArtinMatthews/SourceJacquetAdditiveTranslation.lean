module

public import ArtinMatthews.SourceJacquetHaar
public import ArtinMatthews.StandardLocalConductor
public import ArtinMatthews.StandardLocalBall
public import ArtinMatthews.StandardLocalFourier
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

/-! Actual additive Haar translations on the Jacquet balls. Each local
point is in every sufficiently large ball, and translation by that
point preserves the restricted Haar measure on those balls. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical Filter
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "B" => sourceLocalBall K P
local notation "μ₀" => sourceJacquetHaar K P
local notation "ν₀" => sourceLocalValuation K P

theorem sourceJacquetBall_eventually_contains (t : L) :
    ∀ᶠ N : ℕ in atTop, t ∈ B (N : ℤ) := by
  by_cases ht : t = 0
  · subst t
    exact Eventually.of_forall (fun N => by
      change ν₀ 0 ≤ WithZero.exp (N : ℤ)
      rw [map_zero]
      exact zero_le)
  · have hv := WithZero.exp_log ((Valuation.ne_zero_iff ν₀).mpr ht)
    filter_upwards [eventually_ge_atTop (WithZero.log (ν₀ t)).toNat] with N hN
    change ν₀ t ≤ WithZero.exp (N : ℤ)
    rw [← hv, WithZero.exp_le_exp]
    omega

theorem sourceJacquetBall_translate_mem_iff (n : ℤ) (t x : L) (ht : t ∈ B n) :
    x + t ∈ B n ↔ x ∈ B n := by
  let H := (sourceLocalOpenBall K P n).toAddSubgroup
  have ht' : t ∈ H := ht
  change x + t ∈ H ↔ x ∈ H
  constructor
  · intro h
    simpa only [add_neg_cancel_right] using H.add_mem h (H.neg_mem ht')
  · intro h
    exact H.add_mem h ht'

theorem sourceJacquetBall_translate_measurePreserving (n : ℤ) (t : L) (ht : t ∈ B n) :
    MeasurePreserving (fun x : L => x + t) (Measure.restrict μ₀ (B n)) (Measure.restrict μ₀ (B n)) := by
  let μ := μ₀
  let : μ.IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  let e := MeasurableEquiv.addRight t
  have he : MeasurePreserving e μ μ := measurePreserving_add_right μ t
  have hset : e ⁻¹' B n = B n := Set.ext (fun x => sourceJacquetBall_translate_mem_iff K P n t x ht)
  have h := he.restrict_preimage_emb e.measurableEmbedding (B n)
  rw [hset] at h
  exact h

theorem sourceJacquetBall_translate_integrable_iff {V : Type*} [NormedAddCommGroup V]
    (n : ℤ) (t : L) (ht : t ∈ B n) (f : L → V) :
    IntegrableOn (fun x => f (x + t)) (B n) μ₀ ↔ IntegrableOn f (B n) μ₀ :=
  (sourceJacquetBall_translate_measurePreserving K P n t ht).integrable_comp_emb (g := f)
    (MeasurableEquiv.addRight t).measurableEmbedding

theorem sourceJacquetBall_translate_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℤ) (t : L) (ht : t ∈ B n) (f : L → V) :
    (∫ x in B n, f (x + t) ∂μ₀) = ∫ x in B n, f x ∂μ₀ :=
  (sourceJacquetBall_translate_measurePreserving K P n t ht).integral_comp
    (MeasurableEquiv.addRight t).measurableEmbedding f

end
end ArtinMatthews
