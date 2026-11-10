module

public import ArtinMatthews.AdicIntegerResidueEquiv
public import ArtinMatthews.IntegerOpenSubgroup
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import ArtinMatthews.CompactFiniteAverage
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual normalized Haar measure and residue weights for the
exterior Jacquet shells. The completed residue reduction is transported
through the proved integral quotient equivalence. Its finite averaging
law uses actual Haar translations, with no fiber-mass premise. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain LocalFieldTheory QuadraticWeil MeasureTheory TopologicalSpace
open LocalFieldTheory.IsNonarchimedeanLocalField
open scoped NumberField ValuativeRel Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F))

local instance jacquetAdicRelation : ValuativeRel (P.adicCompletion F) := adicRelation F P
local instance jacquetAdicLocalField : IsNonarchimedeanLocalField (P.adicCompletion F) := adicLocalField F P
local instance jacquetAdicMeasurable : MeasurableSpace (P.adicCompletion F) := borel (P.adicCompletion F)
local instance jacquetAdicBorel : BorelSpace (P.adicCompletion F) := ⟨rfl⟩

abbrev sourceJacquetIntegers := integerOpenSubgroup (P.adicCompletion F)

def sourceJacquetCompact : PositiveCompacts (P.adicCompletion F) :=
  ⟨⟨sourceJacquetIntegers F P, integerOpenSubgroup_compact _⟩, by
    rw [(sourceJacquetIntegers F P).isOpen.interior_eq]
    exact ⟨0, (sourceJacquetIntegers F P).zero_mem⟩⟩

def sourceJacquetHaar : Measure (P.adicCompletion F) :=
  Measure.addHaarMeasure (sourceJacquetCompact F P)

theorem sourceJacquetHaar_isAddHaar : (sourceJacquetHaar F P).IsAddHaarMeasure := by
  unfold sourceJacquetHaar
  infer_instance

theorem sourceJacquetHaar_integers : sourceJacquetHaar F P (sourceJacquetIntegers F P) = 1 :=
  Measure.addHaarMeasure_self (K₀ := sourceJacquetCompact F P)

def sourceJacquetReduction : sourceJacquetIntegers F P →+ ((𝓞 F) ⧸ P.asIdeal) :=
  (adicIntegerResidueEquiv F P).symm.toAddMonoidHom.comp (integerReduction (P.adicCompletion F))

theorem sourceJacquetReduction_surjective : Function.Surjective (sourceJacquetReduction F P) :=
  (adicIntegerResidueEquiv F P).symm.surjective.comp (integerReduction_surjective (P.adicCompletion F))

theorem sourceJacquetReduction_eq_iff (x y : sourceJacquetIntegers F P) :
    sourceJacquetReduction F P x = sourceJacquetReduction F P y ↔
      ‖(x : P.adicCompletion F) - (y : P.adicCompletion F)‖ < 1 := by
  let C := P.adicCompletion F
  let ν : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  change (adicIntegerResidueEquiv F P).symm (integerReduction C x) =
    (adicIntegerResidueEquiv F P).symm (integerReduction C y) ↔ _
  rw [(adicIntegerResidueEquiv F P).symm.injective.eq_iff, ← sub_eq_zero, ← map_sub,
    integerReduction_apply, adic_residue_eq_zero_iff]
  change ValuativeRel.valuation C ((x : C) - (y : C)) < 1 ↔ ‖(x : C) - (y : C)‖ < 1
  exact ((Valuation.vlt_one_iff (ValuativeRel.valuation C)).symm.trans
    (Valuation.vlt_one_iff ν)).trans Valued.toNormedField.norm_lt_one_iff.symm

def sourceJacquetWeight (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ) (x : P.adicCompletion F) : ℂ :=
  if hx : x ∈ sourceJacquetIntegers F P then χ (sourceJacquetReduction F P ⟨x, hx⟩) else 0

theorem sourceJacquetWeight_on_integers (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ)
    (x : sourceJacquetIntegers F P) :
    sourceJacquetWeight F P χ x = χ (sourceJacquetReduction F P x) := by
  rw [sourceJacquetWeight, dite_eq_left x.property]

theorem sourceJacquetWeight_locallyConstant (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ) :
    IsLocallyConstant (sourceJacquetWeight F P χ) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  by_cases hx : x ∈ sourceJacquetIntegers F P
  · refine ⟨(sourceJacquetIntegers F P : Set _) ∩ Metric.ball x 1,
      (sourceJacquetIntegers F P).isOpen.inter Metric.isOpen_ball,
      ⟨hx, Metric.mem_ball_self zero_lt_one⟩, ?_⟩
    intro y hy
    let yU : sourceJacquetIntegers F P := ⟨y, hy.1⟩
    let xU : sourceJacquetIntegers F P := ⟨x, hx⟩
    have he : sourceJacquetReduction F P yU = sourceJacquetReduction F P xU := by
      apply (sourceJacquetReduction_eq_iff F P _ _).mpr
      simpa only [Metric.mem_ball, dist_eq_norm] using hy.2
    exact (sourceJacquetWeight_on_integers F P χ yU).trans
      ((congrArg χ he).trans (sourceJacquetWeight_on_integers F P χ xU).symm)
  · refine ⟨(sourceJacquetIntegers F P : Set _)ᶜ,
      (sourceJacquetIntegers F P).isClosed.isOpen_compl, hx, ?_⟩
    intro y hy
    have hy' : y ∉ sourceJacquetIntegers F P := hy
    simp only [sourceJacquetWeight, dite_eq_right hy', dite_eq_right hx]

theorem sourceJacquetWeight_average (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ) :
    (∫ x in (sourceJacquetIntegers F P : Set (P.adicCompletion F)),
      sourceJacquetWeight F P χ x ∂(sourceJacquetHaar F P)) =
        (∑' z : (𝓞 F) ⧸ P.asIdeal, χ z) / (Ideal.absNorm P.asIdeal : ℂ) := by
  let : (sourceJacquetHaar F P).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar F P
  let : Finite ((𝓞 F) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 F) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card ((𝓞 F) ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [compact_finite_integral (sourceJacquetHaar F P) (sourceJacquetIntegers F P)
    (integerOpenSubgroup_compact _) (sourceJacquetReduction F P)
    (sourceJacquetReduction_surjective F P) χ (sourceJacquetWeight F P χ)
    (sourceJacquetWeight_locallyConstant F P χ).continuous (sourceJacquetWeight_on_integers F P χ)]
  simp only [Measure.real, sourceJacquetHaar_integers, ENNReal.toReal_one, Complex.ofReal_one,
    one_mul, hcard, tsum_fintype]

end
end ArtinMatthews
