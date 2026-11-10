module

public import ArtinMatthews.SourceSLocalAdditiveProbeBinding
public import ArtinMatthews.SourcePrincipalBallQuotientCoverage
public import ArtinMatthews.StandardLocalBallDilation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed compact source S-local box has one clearing denominator.
Only the archimedean coordinates dilate, at exactly the N^(1/[F:Q]) scale. -/
namespace ArtinMatthews.SourcePhysical

open NumberField NumberField.InfinitePlace IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "S" => sourceHilbertSet F S₀
local notation "T" => sourceHilbertSeed F S₀
local notation "R" => sourceRing F S₀
local notation "d" => principalizingDenominator T
local notation "FS" => SLocalAdditiveCompletionSpace F S

private theorem sourceLocalNorm_le_one_iff (P : HeightOneSpectrum (𝓞 F)) (x : P.adicCompletion F) :
    ‖x‖ ≤ 1 ↔ sourceLocalValuation F P x ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, sourceLocalValuation]
  have hv : sourceLocalValuation F P x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hq : 1 < (Ideal.absNorm P.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P
  rw [sourceLocalNorm_eq_zpow F P x hx]
  calc
    _ ↔ WithZero.log (sourceLocalValuation F P x) ≤ 0 := by
      simpa only [zpow_zero] using
        (zpow_le_zpow_iff_right₀ hq (m := WithZero.log (sourceLocalValuation F P x)) (n := 0))
    _ ↔ _ := by
      rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.log_exp]

private theorem sourcePrincipalDenominator_completion_norm_lt_one (v : S) :
    ‖((d : F) : v.val.adicCompletion F)‖ < 1 := by
  let x : v.val.adicCompletion F := (d : F)
  have hd : (d : F) ≠ 0 := Subtype.coe_injective.ne (principalizingDenominator_ne_zero T)
  have hx : x ≠ 0 := (map_ne_zero (algebraMap F (v.val.adicCompletion F))).mpr hd
  have hval : sourceLocalValuation F v.val x < 1 := by
    change Valued.v ((d : F) : v.val.adicCompletion F) < 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (v.val.valuation_lt_one_iff_mem (K := F) d).mpr
      ((mem_denominatorSupport d (principalizingDenominator_ne_zero T) v.val).mp v.property)
  have hv : sourceLocalValuation F v.val x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hlog : WithZero.log (sourceLocalValuation F v.val x) < 0 := by
    rw [← WithZero.exp_lt_one_iff, WithZero.exp_log hv]
    exact hval
  have hq : 1 < (Ideal.absNorm v.val.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val
  change ‖x‖ < 1
  rw [sourceLocalNorm_eq_zpow F v.val x hx]
  simpa only [zpow_zero] using
    (zpow_lt_zpow_iff_right₀ hq (m := WithZero.log (sourceLocalValuation F v.val x)) (n := 0)).mpr hlog

/-- A single actual power of the principalizing denominator puts every
finite coordinate of the compact box in the local integer rings. -/
theorem exists_sourceCompactClearingDenominator (B : Set FS) (hB : IsCompact B) :
    ∃ δ : 𝓞 F, δ ≠ 0 ∧
      (∀ P : HeightOneSpectrum (𝓞 F), P ∉ S → P.valuation F (δ : F) = 1) ∧
      ∀ x ∈ B, ∀ v : S, ‖((δ : F) : v.val.adicCompletion F) * x.2 v‖ ≤ 1 := by
  have hb (v : S) : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ B, ‖x.2 v‖ ≤ C := by
    let f (x : FS) := x.2 v
    have hf : Continuous f := (continuous_apply v).comp continuous_snd
    obtain ⟨C, hC⟩ := (hB.image hf).isBounded.exists_norm_le
    exact ⟨max 1 C, zero_lt_one.trans_le (le_max_left _ _), fun x hx =>
      (hC (f x) ⟨x, hx, rfl⟩).trans (le_max_right _ _)⟩
  choose C hC0 hC using hb
  have hpow (v : S) : ∃ k : ℕ, ‖((d : F) : v.val.adicCompletion F)‖ ^ k < 1 / C v :=
    exists_pow_lt_of_lt_one (one_div_pos.mpr (hC0 v))
      (sourcePrincipalDenominator_completion_norm_lt_one F S₀ v)
  choose k hk using hpow
  let n := (Finset.univ : Finset S).sup k
  refine ⟨d ^ n, pow_ne_zero _ (principalizingDenominator_ne_zero T), ?_, ?_⟩
  · intro P hP
    change P.valuation F (algebraMap (𝓞 F) F (d ^ n)) = 1
    rw [map_pow, map_pow, sourcePrincipalDenominator_valuation_exterior F T P hP, one_pow]
  · intro x hx v
    have hkn : k v ≤ n := Finset.le_sup (f := k) (Finset.mem_univ v)
    let a : ℝ := ‖((d : F) : v.val.adicCompletion F)‖
    have ha : a ≤ 1 := (sourcePrincipalDenominator_completion_norm_lt_one F S₀ v).le
    change ‖algebraMap F (v.val.adicCompletion F) (algebraMap (𝓞 F) F (d ^ n)) * x.2 v‖ ≤ 1
    rw [map_pow, map_pow, norm_mul, norm_pow]
    change a ^ n * ‖x.2 v‖ ≤ 1
    exact (mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) ha hkn) (hC v x hx)
      (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)).trans
        ((lt_div_iff₀ (hC0 v)).mp (hk v)).le

variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

def sourceScaledLatticeRows (B : Set FS) (N : ℝ) : Set R :=
  {m | sLocalRingDiagonal F S (m : F) ∈
    (fun x : FS => sourceSLocalUnitAdditivePoint F S (sLocalPositiveScaling F hζ S N) * x) '' B}

/-- Every scaled lattice row has an actual integral coordinate after one
fixed clearing denominator. Its mixed norm grows at the literal source
radial exponent, uniformly in the scale. -/
theorem exists_sourceScaledLatticeRows_integral (B : Set FS) (hB : IsCompact B) :
    ∃ δ : 𝓞 F, δ ≠ 0 ∧ (∀ P : HeightOneSpectrum (𝓞 F), P ∉ S → P.valuation F (δ : F) = 1) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → ∀ m ∈ sourceScaledLatticeRows F S₀ hζ B N,
        ∃ n : 𝓞 F, (n : F) = (m : F) * (δ : F) ∧
          ‖mixedEmbedding F (n : F)‖ ≤ C * N ^ (Module.finrank ℚ F : ℝ)⁻¹ := by
  obtain ⟨δ, hδ, hδS, hfin⟩ := exists_sourceCompactClearingDenominator F S₀ B hB
  have hbound (w : InfinitePlace F) : ∃ C : ℝ, ∀ x ∈ B, ‖x.1 w‖ ≤ C := by
    let f (x : FS) := x.1 w
    have hf : Continuous f := (continuous_apply w).comp continuous_fst
    obtain ⟨C, hC⟩ := (hB.image hf).isBounded.exists_norm_le
    exact ⟨C, fun x hx => hC (f x) ⟨x, hx, rfl⟩⟩
  choose C hC using hbound
  let A : ℝ := 1 + ∑ w, |C w|
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAC (w : InfinitePlace F) : C w ≤ A := by
    have hsum := Finset.single_le_sum (s := (Finset.univ : Finset (InfinitePlace F)))
      (f := fun w => |C w|) (fun i _ => abs_nonneg _) (Finset.mem_univ w)
    dsimp only [A]
    linarith [le_abs_self (C w)]
  let D := 1 + ‖mixedEmbedding F (δ : F)‖
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨δ, hδ, hδS, A * D, mul_pos hA hD, fun N hN m hm => ?_⟩
  obtain ⟨x, hx, he⟩ := hm
  have hval (P : HeightOneSpectrum (𝓞 F)) : P.valuation F ((m : F) * (δ : F)) ≤ 1 := by
    by_cases hP : P ∈ S
    · let v : S := ⟨P, hP⟩
      have heP := congrArg (fun y : FS => y.2 v) he
      change (((sLocalPositiveScaling F hζ S N).2 v : P.adicCompletion F) * x.2 v) =
        (algebraMap F (P.adicCompletion F) (m : F)) at heP
      rw [sLocalPositiveScaling_finite, Units.val_one, one_mul] at heP
      have hnorm : ‖algebraMap F (P.adicCompletion F) ((m : F) * (δ : F))‖ ≤ 1 := by
        rw [map_mul, ← heP, mul_comm]
        exact hfin x hx v
      have h := (sourceLocalNorm_le_one_iff F P _).mp hnorm
      change Valued.v (((m : F) * (δ : F) : F) : P.adicCompletion F) ≤ 1 at h
      rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    · rw [map_mul, hδS P hP, mul_one]
      exact m.property P hP
  obtain ⟨n, hn⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hval
  refine ⟨n, hn, ?_⟩
  have harch : ‖mixedEmbedding F (m : F)‖ ≤ A * N ^ (Module.finrank ℚ F : ℝ)⁻¹ := by
    rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
    apply Finset.sup'_le
    intro w _
    rw [mixedEmbedding.normAtPlace_apply]
    have hew := congrArg (fun y : FS => y.1 w) he
    change (((sLocalPositiveScaling F hζ S N).1 w : w.Completion) * x.1 w) =
      (algebraMap F w.Completion (m : F)) at hew
    have hw : ‖algebraMap F w.Completion (m : F)‖ = w (m : F) := by
      exact (InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm (m : F))).trans
        (congrArg w ((WithAbs.equiv w.1).apply_symm_apply (m : F)))
    rw [← hw, ← hew, norm_mul, sLocalPositiveScaling_infinite_norm, Real.rpow_def_of_pos hN,
      div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hC w x hx).trans (hAC w)) (Real.exp_pos _).le
  change (n : F) = (m : F) * (δ : F) at hn
  rw [hn, map_mul]
  calc
    _ ≤ ‖mixedEmbedding F (m : F)‖ * ‖mixedEmbedding F (δ : F)‖ := norm_mul_le _ _
    _ ≤ (A * N ^ (Module.finrank ℚ F : ℝ)⁻¹) * D :=
      mul_le_mul harch (by dsimp only [D]; linarith) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end
end ArtinMatthews.SourcePhysical
