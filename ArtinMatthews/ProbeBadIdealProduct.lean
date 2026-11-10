module

public import ArtinMatthews.ProbeBadIdealGaussHolomorphy
public import ArtinMatthews.ProbeBadIdealRegions
public import ArtinMatthews.ProbeBadPrimeFiniteProduct
public import ArtinMatthews.ProbeBadPrimeProductBound
public import ArtinMatthews.ProbeIdealCoefficientBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Actual good/bad products at arbitrary prime ideals. The finite bad
factors have a field-uniform local bound, so the true ideal prime-support
estimate yields an arbitrarily small power of the ideal parameter. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain Set
open scoped NumberField Classical BigOperators Topology
noncomputable section

namespace ProbeBadIdealData
variable {K : Type*} [Field K] [NumberField K] {P : HeightOneSpectrum (𝓞 K)}
variable (D : ProbeBadIdealData K P)

theorem correction_norm_sub_one_le (q : ArtinMatthews.ProbeCoordinates)
    (hq : q ∈ ArtinMatthews.probeEulerDomain) :
    ‖D.correction q - 1‖ ≤ 36 * (Ideal.absNorm P.asIdeal : ℝ) ^ (-(1 / 4000 : ℝ)) := by
  obtain ⟨hγ, hν, hθ⟩ := D.phase_norms
  exact probeBadIdealSourceCorrection_regions K P D.character D.order_six D.minus_one
    D.valuation D.valuation_pos D.gamma D.vartheta D.theta hγ hν hθ D.norm_large q hq

theorem correction_norm_le (q : ArtinMatthews.ProbeCoordinates)
    (hq : q ∈ ArtinMatthews.probeEulerDomain) : ‖D.correction q‖ ≤ 64 := by
  have hp : (Ideal.absNorm P.asIdeal : ℝ) ^ (-(1 / 4000 : ℝ)) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (probeIdealNorm_one_le K P) (by norm_num : -(1 / 4000 : ℝ) ≤ 0)
  have H := D.correction_norm_sub_one_le q hq
  have ht := norm_add_le (D.correction q - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at ht
  linarith

end ProbeBadIdealData

variable (K : Type*) [Field K] [NumberField K]

theorem exists_probeBadIdealFiniteProduct_subpower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)), I ≠ ⊥ →
      ∀ (T : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ P ∈ T, P.asIdeal ∈ HeckeIdealMobius.primeSupport K I) →
      ∀ (D : ∀ P : T, ProbeBadIdealData K P.val) (q : ArtinMatthews.ProbeCoordinates),
      q ∈ ArtinMatthews.probeEulerDomain →
      ‖probeBadIdealFiniteProduct K T D q‖ ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := exists_probe_primeSupport_product_bound K ε hε
  refine ⟨C, hC, ?_⟩
  intro I hI T hT D q hq
  have hc : (64 : ℝ) ^ (HeckeIdealMobius.primeSupport K I).card ≤
      C * (Ideal.absNorm I : ℝ) ^ ε := by
    simpa using h I hI (fun _ => (64 : ℂ)) (by norm_num)
  have himage : T.image (fun P => P.asIdeal) ⊆ HeckeIdealMobius.primeSupport K I := by
    intro J hJ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hJ
    exact hT P hP
  have hcard : T.card ≤ (HeckeIdealMobius.primeSupport K I).card := by
    calc
      _ = (T.image (fun P => P.asIdeal)).card :=
        (Finset.card_image_of_injective T HeightOneSpectrum.asIdeal_injective).symm
      _ ≤ _ := Finset.card_le_card himage
  calc
    _ ≤ ∏ _P : T, (64 : ℝ) := by
      rw [probeBadIdealFiniteProduct, norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P _ => (D P).correction_norm_le q hq)
    _ = (64 : ℝ) ^ T.card := by simp
    _ ≤ (64 : ℝ) ^ (HeckeIdealMobius.primeSupport K I).card :=
      pow_le_pow_right₀ (by norm_num) hcard
    _ ≤ _ := hc

theorem exists_probeBadIdealFiniteProduct_fixed_support_bound
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Ideal (𝓞 K)), U ≠ ⊥ →
      ∀ (T : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ P ∈ T, P.asIdeal ∈ HeckeIdealMobius.primeSupport K (U * R)) →
      ∀ (D : ∀ P : T, ProbeBadIdealData K P.val) (q : ArtinMatthews.ProbeCoordinates),
      q ∈ ArtinMatthews.probeEulerDomain →
      ‖probeBadIdealFiniteProduct K T D q‖ ≤ C * (Ideal.absNorm U : ℝ) ^ ε := by
  obtain ⟨B, hB, h⟩ := exists_probeBadIdealFiniteProduct_subpower_bound K ε hε
  have hRN : 0 < (Ideal.absNorm R : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hR)
  refine ⟨B * (Ideal.absNorm R : ℝ) ^ ε, mul_pos hB (Real.rpow_pos_of_pos hRN _), ?_⟩
  intro U hU T hT D q hq
  have H := h (U * R) (mul_ne_zero hU hR) T hT D q hq
  rw [map_mul, Nat.cast_mul, Real.mul_rpow (by positivity) hRN.le] at H
  exact H.trans_eq (by ring)

def probeGoodBadIdealProduct (S : Finset (ArtinMatthews.ProbePrime K))
    (a b c : ArtinMatthews.ProbePrime K → ℂ) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (D : ∀ P : T, ProbeBadIdealData K P.val) (q : ArtinMatthews.ProbeCoordinates) : ℂ :=
  ArtinMatthews.probeEulerProduct K S a b c q * probeBadIdealFiniteProduct K T D q

theorem probeGoodBadIdealProduct_differentiableOn (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : ArtinMatthews.probePrimeCutoff K ⊆ S) (a b c : ArtinMatthews.ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (D : ∀ P : T, ProbeBadIdealData K P.val) :
    DifferentiableOn ℂ (probeGoodBadIdealProduct K S a b c T D)
      (interior ArtinMatthews.probeEulerDomain) :=
  (ArtinMatthews.probeEulerProduct_differentiableOn K S hS a b c ha hb hc).mul
    (probeBadIdealFiniteProduct_differentiableOn K T D)

theorem probeGoodBadIdealProduct_differentiableOn_open (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : ArtinMatthews.probePrimeCutoff K ⊆ S) (a b c : ArtinMatthews.ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (D : ∀ P : T, ProbeBadIdealData K P.val) :
    DifferentiableOn ℂ (probeGoodBadIdealProduct K S a b c T D)
      ArtinMatthews.probeEulerOpenDomain :=
  (probeGoodBadIdealProduct_differentiableOn K S hS a b c ha hb hc T D).mono
    ArtinMatthews.probeEulerOpenDomain_subset_interior

theorem exists_probeGoodBadIdealProduct_fixed_support_bound
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (ArtinMatthews.ProbePrime K)),
      ArtinMatthews.probePrimeCutoff K ⊆ S →
      ∀ (a b c : ArtinMatthews.ProbePrime K → ℂ),
      (∀ P, ‖a P‖ ≤ 1) → (∀ P, ‖b P‖ ≤ 1) → (∀ P, ‖c P‖ ≤ 1) →
      ∀ (U : Ideal (𝓞 K)), U ≠ ⊥ →
      ∀ (T : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ P ∈ T, P.asIdeal ∈ HeckeIdealMobius.primeSupport K (U * R)) →
      ∀ (D : ∀ P : T, ProbeBadIdealData K P.val) (q : ArtinMatthews.ProbeCoordinates),
      q ∈ ArtinMatthews.probeEulerDomain →
      ‖probeGoodBadIdealProduct K S a b c T D q‖ ≤ C * (Ideal.absNorm U : ℝ) ^ ε := by
  obtain ⟨B, hB, hbound⟩ := exists_probeBadIdealFiniteProduct_fixed_support_bound K R hR ε hε
  refine ⟨probeGoodProductUniformBound K * B,
    mul_pos (probeGoodProductUniformBound_pos K) hB, ?_⟩
  intro S hS a b c ha hb hc U hU T hT D q hq
  rw [probeGoodBadIdealProduct, norm_mul]
  have hbad := hbound U hU T hT D q hq
  calc
    _ ≤ probeGoodProductUniformBound K * (B * (Ideal.absNorm U : ℝ) ^ ε) :=
      mul_le_mul (probeEulerProduct_norm_le_uniform K S hS a b c ha hb hc hq) hbad
        (norm_nonneg _) (probeGoodProductUniformBound_pos K).le
    _ = _ := by ring

end
end ArtinMatthews.VaryingKummerAnalytic
