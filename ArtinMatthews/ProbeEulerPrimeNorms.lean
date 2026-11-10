module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusMass
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

/-! True ideal-prime summability and a finite cutoff for the source-05
good-prime correction factors. The cutoff is chosen from numerical decay;
the summability is inherited from the actual nonzero-ideal norm series. -/

namespace ArtinMatthews

noncomputable section
open NumberField IsDedekindDomain Set Filter
open scoped NumberField Classical BigOperators Topology

abbrev ProbePrime (K : Type*) [Field K] [NumberField K] :=
  HeightOneSpectrum (𝓞 K)

variable (K : Type*) [Field K] [NumberField K]

def probePrimeWeight (P : ProbePrime K) : ℝ :=
  (Ideal.absNorm P.asIdeal : ℝ) ^ (-(1 + 1 / 4000 : ℝ))

theorem probePrimeWeight_nonneg (P : ProbePrime K) : 0 ≤ probePrimeWeight K P :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem probePrimeWeight_summable : Summable (probePrimeWeight K) := by
  have h := (VaryingKummerAnalytic.HeckeIdealMobius.normSeries_summable K
    (by norm_num : (0 : ℝ) < 1 / 4000)).comp_injective
      (i := fun P : ProbePrime K => (⟨P.asIdeal, P.ne_bot⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥}))
      (by intro P Q h; exact HeightOneSpectrum.asIdeal_injective (congrArg Subtype.val h))
  exact h

theorem probePrimeWeight_tsum_le :
    ∑' P, probePrimeWeight K P ≤
      VaryingKummerAnalytic.HeckeIdealMobius.normSeries K (1 / 4000) := by
  apply Summable.tsum_le_tsum_of_inj
    (fun P : ProbePrime K => (⟨P.asIdeal, P.ne_bot⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥}))
    (by intro P Q h; exact HeightOneSpectrum.asIdeal_injective (congrArg Subtype.val h))
  · intro I hI
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · intro P
    exact le_rfl
  · exact probePrimeWeight_summable K
  · exact VaryingKummerAnalytic.HeckeIdealMobius.normSeries_summable K (by norm_num)

theorem exists_probeEulerCutoff : ∃ N : ℕ, 1 ≤ N ∧ ∀ Q : ℝ, (N : ℝ) ≤ Q →
    1 ≤ Q ∧ Q ^ (-(299 / 100000 : ℝ)) ≤ 1 / 2 ∧
      160 * Q ^ (-(1 + 1 / 4000 : ℝ)) ≤ 1 / 2 := by
  have hsmall := (tendsto_rpow_neg_atTop
    (by norm_num : (0 : ℝ) < 299 / 100000)).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have herror := ((tendsto_rpow_neg_atTop
    (by norm_num : (0 : ℝ) < 1 + 1 / 4000)).const_mul 160).eventually
      (gt_mem_nhds (by norm_num : (160 : ℝ) * 0 < 1 / 2))
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hsmall.and herror)
  obtain ⟨N, hN⟩ := exists_nat_gt (max R 1)
  refine ⟨N, ?_, fun Q hQ => ?_⟩
  · have : (1 : ℝ) < N := (le_max_right R 1).trans_lt hN
    exact_mod_cast this.le
  · have hQR : R ≤ Q := (le_max_left R 1).trans (hN.le.trans hQ)
    exact ⟨(le_max_right R 1).trans (hN.le.trans hQ), (hR Q hQR).1.le,
      (hR Q hQR).2.le⟩

def probeEulerCutoff : ℕ := exists_probeEulerCutoff.choose

theorem probeEulerCutoff_spec {Q : ℝ} (hQ : (probeEulerCutoff : ℝ) ≤ Q) :
    1 ≤ Q ∧ Q ^ (-(299 / 100000 : ℝ)) ≤ 1 / 2 ∧
      160 * Q ^ (-(1 + 1 / 4000 : ℝ)) ≤ 1 / 2 :=
  exists_probeEulerCutoff.choose_spec.2 Q hQ

theorem probePrimeCutoff_finite :
    {P : ProbePrime K | Ideal.absNorm P.asIdeal ≤ probeEulerCutoff}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le probeEulerCutoff).preimage
    HeightOneSpectrum.asIdeal_injective.injOn

def probePrimeCutoff : Finset (ProbePrime K) := (probePrimeCutoff_finite K).toFinset

theorem mem_probePrimeCutoff (P : ProbePrime K) :
    P ∈ probePrimeCutoff K ↔ Ideal.absNorm P.asIdeal ≤ probeEulerCutoff :=
  Set.Finite.mem_toFinset _

abbrev ProbeGoodPrime (S : Finset (ProbePrime K)) := {P : ProbePrime K // P ∉ S}

theorem probeGoodPrime_norm_bounds (S : Finset (ProbePrime K))
    (hS : probePrimeCutoff K ⊆ S) (P : ProbeGoodPrime K S) :
    1 ≤ (Ideal.absNorm P.val.asIdeal : ℝ) ∧
      (Ideal.absNorm P.val.asIdeal : ℝ) ^ (-(299 / 100000 : ℝ)) ≤ 1 / 2 ∧
      160 * probePrimeWeight K P.val ≤ 1 / 2 := by
  have hN : probeEulerCutoff < Ideal.absNorm P.val.asIdeal := by
    by_contra! h
    exact P.property (hS ((mem_probePrimeCutoff K P.val).mpr h))
  exact probeEulerCutoff_spec (by exact_mod_cast hN.le)

theorem probeGoodPrime_majorant_summable (S : Finset (ProbePrime K)) :
    Summable (fun P : ProbeGoodPrime K S => 240 * probePrimeWeight K P.val) :=
  ((probePrimeWeight_summable K).subtype (fun P => P ∉ S)).mul_left 240

end
end ArtinMatthews
