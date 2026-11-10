module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicMoment.Estimates.HeckeDualMoment
public import OAI.NumberTheory.CubicMoment.Estimates.OrdinaryMixedSieve
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.CubicMoment.Estimates.DualPolynomialScale
public import OAI.NumberTheory.CubicMoment.Estimates.IdealCubicMoments
public import OAI.NumberTheory.CubicMoment.Estimates.IdealEulerExclusion


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! The ordinary mixed sieve on the normalized dual ideal blocks. All
coefficient bounds and the number of ideals are derived explicitly. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma ideal_support_card_le {S : Finset EisensteinIdealExponent} {Y : ℝ}
    (hY : 0 ≤ Y) (hS : ∀ ν ∈ S, idealExponentNorm ν ≤ Y) :
    (S.card : ℝ) ≤ 18*Y := by
  have hsub : S ⊆ fullIdealBall Y := fun ν hν => mem_fullIdealBall.mpr (hS ν hν)
  have hcard : S.card ≤ (nonzeroNormBall Y).card :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le)
  exact (Nat.cast_le.mpr hcard).trans (nonzeroNormBall_card_le hY)

lemma normalizedDualPolynomial_mixed (S : Finset EisensteinIdealExponent)
    (a b : Eisenstein) (J u : ℝ) :
    normalizedDualPolynomial S (fun ν => mixedCubic a b (idealExponentGenerator ν))
      idealExponentNorm J u =
      ∑ ν ∈ S, (((J/idealExponentNorm ν)^(1/2:ℝ):ℝ)*mellinPhase u (idealExponentNorm ν))*
        mixedCubic a b (idealExponentGenerator ν) := by
  unfold normalizedDualPolynomial
  apply Finset.sum_congr rfl
  intro ν hν
  ring

/-- Complete dual ideal supports, including the ramified prime, satisfy
the ordinary sieve bound uniformly in their common norm twist. -/
theorem normalized_ideal_mixed_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (Eisenstein × Eisenstein))
      (S : Finset EisensteinIdealExponent) (Q Y J u : ℝ),
      1 ≤ Q → 1 ≤ Y → 0 < J →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ ν ∈ S, J ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ Y) →
      (∑ p ∈ P, ‖normalizedDualPolynomial S
        (fun ν => mixedCubic p.1 p.2 (idealExponentGenerator ν))
        idealExponentNorm J u‖^2) ≤ C*Q^ε*(Q^2+Y)*Y := by
  obtain ⟨C,hC,hbound⟩ := ideal_mixed_moment hHuxley hε
  refine ⟨18*C,by positivity,?_⟩
  intro P S Q Y J u hQ hY hJ hP hS
  let v : EisensteinIdealExponent → ℂ := fun ν =>
    (((J/idealExponentNorm ν)^(1/2:ℝ):ℝ)*mellinPhase u (idealExponentNorm ν))
  have hv : ∀ ν ∈ S, ‖v ν‖ ≤ 1 := by
    intro ν hν
    dsimp [v]
    rw [norm_mul,mellinPhase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (div_nonneg hJ.le (idealExponentNorm_pos ν).le) _)]
    exact dual_dyad_weight_le_one hJ (hS ν hν).1
  have henergy : (∑ ν ∈ S, ‖v ν‖^2) ≤ 18*Y := by
    calc
      _ ≤ ∑ _ν ∈ S, (1:ℝ) := Finset.sum_le_sum (fun ν hν => by
        simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) (hv ν hν) 2)
      _ = (S.card : ℝ) := by simp
      _ ≤ 18*Y := ideal_support_card_le (by linarith) (fun ν hν => (hS ν hν).2)
  have h := hbound P S Q Y hQ hY hP (fun ν hν => (hS ν hν).2) v
  simp_rw [normalizedDualPolynomial_mixed]
  calc
    _ ≤ C*Q^ε*(Q^2+Y)*∑ ν ∈ S, ‖v ν‖^2 := h
    _ ≤ C*Q^ε*(Q^2+Y)*(18*Y) := mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
