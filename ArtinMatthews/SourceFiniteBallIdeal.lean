module

public import ArtinMatthews.StandardAdelicSIntegerPhase
public import ArtinMatthews.StandardLocalConductor
public import ArtinMatthews.SourceFractionalIdealValuation
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

/-! A finite family of genuine local balls gives the literal fractional
ideal with those valuation exponents, intersected with the exterior
integer conditions. Membership, counts, and norm are derived. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain FractionalIdeal StandardAdelic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "FI" => FractionalIdeal (𝓞 K)⁰ K

def sourceFiniteBallIdeal (e : S → ℤ) : FI :=
  ∏ v : S, (v.val.asIdeal : FI) ^ e v

theorem sourceFiniteBallIdeal_ne_zero (e : S → ℤ) : sourceFiniteBallIdeal K S e ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro v _
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.val.ne_bot)

theorem sourceFiniteBallIdeal_count (e : S → ℤ) (P : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K P (sourceFiniteBallIdeal K S e) = if h : P ∈ S then e ⟨P, h⟩ else 0 := by
  unfold sourceFiniteBallIdeal
  rw [FractionalIdeal.count_prod K P _ _ (fun v _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.val.ne_bot))]
  by_cases hP : P ∈ S
  · rw [dite_eq_left hP, Finset.sum_eq_single (⟨P, hP⟩ : S)]
    · exact FractionalIdeal.count_zpow_self K P _
    · intro v _ hv
      have h : v.val ≠ P := fun he => hv (Subtype.ext he)
      rw [FractionalIdeal.count_zpow K P, FractionalIdeal.count_maximal_coprime K P h, mul_zero]
    · intro hn
      exact (hn (Finset.mem_univ _)).elim
  · rw [dite_eq_right hP]
    apply Finset.sum_eq_zero
    intro v _
    have h : v.val ≠ P := fun he => hP (he ▸ v.property)
    rw [FractionalIdeal.count_zpow K P, FractionalIdeal.count_maximal_coprime K P h, mul_zero]

theorem sourceFiniteBallIdeal_norm (e : S → ℤ) :
    (FractionalIdeal.absNorm (sourceFiniteBallIdeal K S e) : ℝ) =
      ∏ v : S, (Ideal.absNorm v.val.asIdeal : ℝ) ^ e v := by
  have h : FractionalIdeal.absNorm (sourceFiniteBallIdeal K S e) =
      ∏ v : S, (Ideal.absNorm v.val.asIdeal : ℚ) ^ e v := by
    unfold sourceFiniteBallIdeal
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro v _
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
  rw [h, Rat.cast_prod]
  simp only [Rat.cast_zpow, Rat.cast_natCast]

theorem sourceFiniteBallIdeal_mem_iff (e : S → ℤ) (x : K) :
    x ∈ sourceFiniteBallIdeal K S e ↔
      (∀ P : HeightOneSpectrum (𝓞 K), P ∉ S → P.valuation K x ≤ 1) ∧
      ∀ v : S, algebraMap K (v.val.adicCompletion K) x ∈ sourceLocalBall K v.val (-(e v)) := by
  rw [sourceFractionalIdeal_mem_iff_valuation K _ (sourceFiniteBallIdeal_ne_zero K S e)]
  constructor
  · intro h
    refine ⟨fun P hP => ?_, fun v => ?_⟩
    · simpa only [sourceFiniteBallIdeal_count K S e, dite_eq_right hP, neg_zero, WithZero.exp_zero] using h P
    · change Valued.v (x : v.val.adicCompletion K) ≤ WithZero.exp (-(e v))
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      simpa only [sourceFiniteBallIdeal_count K S e, dite_eq_left v.property] using h v.val
  · rintro ⟨hout, hin⟩ P
    by_cases hP : P ∈ S
    · rw [sourceFiniteBallIdeal_count K S e, dite_eq_left hP]
      have h := hin ⟨P, hP⟩
      change Valued.v (x : P.adicCompletion K) ≤ WithZero.exp (-(e ⟨P, hP⟩)) at h
      rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    · simpa only [sourceFiniteBallIdeal_count K S e, dite_eq_right hP, neg_zero, WithZero.exp_zero] using hout P hP

theorem sourceFiniteBallIdeal_sInteger_mem_iff (e : S → ℤ) (x : sIntegerRing K S) :
    (x : K) ∈ sourceFiniteBallIdeal K S e ↔
      ∀ v : S, algebraMap K (v.val.adicCompletion K) (x : K) ∈ sourceLocalBall K v.val (-(e v)) := by
  rw [sourceFiniteBallIdeal_mem_iff]
  exact and_iff_right x.property

end
end ArtinMatthews.SourcePhysical
