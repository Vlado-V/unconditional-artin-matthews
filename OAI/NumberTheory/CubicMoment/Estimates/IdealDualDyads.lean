module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicMoment.Estimates.HeckeDualContour
public import OAI.NumberTheory.CubicMoment.Estimates.MellinWeights
public import OAI.NumberTheory.CubicMoment.Estimates.ShortMoebius
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
public import OAI.NumberTheory.CubicGram.DyadicRecurrence
public import OAI.NumberTheory.CubicMoment.Estimates.DualPolynomialScale


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Exact dyadic decomposition of the retained full-ideal polynomial.
The square-root normalization changes only coefficients, not characters. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def idealDyadIndex (ν : EisensteinIdealExponent) : ℕ :=
  Nat.log 2 (normNat (idealExponentGenerator ν))

def idealDyad (S : Finset EisensteinIdealExponent) (j : ℕ) : Finset EisensteinIdealExponent :=
  S.filter (fun ν => idealDyadIndex ν = j)

def idealDyadIndices (S : Finset EisensteinIdealExponent) : Finset ℕ := S.image idealDyadIndex

lemma idealDyad_norm {S : Finset EisensteinIdealExponent} {j : ℕ}
    {ν : EisensteinIdealExponent} (hν : ν ∈ idealDyad S j) :
    (2:ℝ)^j ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ 2*(2:ℝ)^j := by
  have hmem : idealExponentGenerator ν ∈ frequencyDyad j :=
    mem_frequencyDyad.mpr ⟨idealExponentGenerator_ne_zero ν,(Finset.mem_filter.mp hν).2⟩
  simpa only [idealExponentNorm,normNat_cast] using frequencyDyad_norm hmem

lemma finite_idealDirichlet_dyad_partition (S : Finset EisensteinIdealExponent)
    (χ : EisensteinIdealExponent → ℂ) (s : ℂ) :
    finiteNormDirichlet S χ idealExponentNorm s =
      ∑ j ∈ idealDyadIndices S, finiteNormDirichlet (idealDyad S j) χ idealExponentNorm s := by
  unfold finiteNormDirichlet idealDyadIndices idealDyad
  exact (Finset.sum_fiberwise_of_maps_to
    (fun ν hν => Finset.mem_image_of_mem idealDyadIndex hν) _).symm

/-- The complete retained polynomial is the sum of normalized dyads;
all coefficient weights are independent of the Hecke conductor. -/
theorem finite_idealDirichlet_normalized_dyads (S : Finset EisensteinIdealExponent)
    (χ : EisensteinIdealExponent → ℂ) (u : ℝ) :
    finiteNormDirichlet S χ idealExponentNorm ((1/2:ℂ)-(u:ℂ)*Complex.I) =
      ∑ j ∈ idealDyadIndices S, (((2:ℝ)^j)^(-(1/2:ℝ)):ℝ)*
        ∑ ν ∈ idealDyad S j,
          (χ ν*((((2:ℝ)^j)/idealExponentNorm ν)^(1/2:ℝ):ℝ))*
            mellinPhase u (idealExponentNorm ν) := by
  rw [finite_idealDirichlet_dyad_partition]
  apply Finset.sum_congr rfl
  intro j hj
  exact finite_dual_dyad_rescale (idealDyad S j) χ idealExponentNorm
    (by positivity) (fun ν _ => idealExponentNorm_pos ν) u

lemma idealDyad_normalized_coefficient_le (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {S : Finset EisensteinIdealExponent} {j : ℕ}
    {ν : EisensteinIdealExponent} (hν : ν ∈ idealDyad S j) :
    ‖χ ν*((((2:ℝ)^j)/idealExponentNorm ν)^(1/2:ℝ):ℝ)‖ ≤ 1 :=
  (norm_dual_dyad_coefficient_le (by positivity) (idealDyad_norm hν).1 (χ ν)).trans (hχ ν)

lemma idealDyadIndices_card_le {J : ℝ} (S : Finset EisensteinIdealExponent)
    (hS : ∀ ν ∈ S, idealExponentNorm ν ≤ J) :
    (idealDyadIndices S).card ≤ Nat.log 2 ⌊J⌋₊+1 := by
  have hsub : idealDyadIndices S ⊆ Finset.range (Nat.log 2 ⌊J⌋₊+1) := by
    intro j hj
    obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hj
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    apply Nat.le_floor
    simpa only [normNat_cast,idealExponentNorm] using hS ν hν
  simpa only [Finset.card_range] using Finset.card_le_card hsub

end CubicFirstMoment

end

end OAI
