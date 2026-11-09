module

public import ArtinMatthews.SourceGlobalCorrection
public import ArtinMatthews.ProbeBadIdealProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source correction is holomorphic on both enlarged
regions and bounded by any positive power of the literal frequency
norm. The bad set is the derived prime support of the source element. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain UniqueFactorizationMonoid AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)
variable (hM : M ≠ ⊥)
variable (hcut : principalAngularCutoff F M ⊆ sourceHilbertSet F S₀)

local notation "S" => sourceHilbertSet F S₀

theorem sourceExterior_norm_cutoff (hcut₀ : probePrimeCutoff F ⊆ S)
    (P : SourceExteriorPrime F S₀) :
    (probeEulerCutoff : ℝ) ≤ Ideal.absNorm P.val.asIdeal := by
  have hn : ¬ Ideal.absNorm P.val.asIdeal ≤ probeEulerCutoff :=
    fun h => P.property (hcut₀ ((mem_probePrimeCutoff F P.val).mpr h))
  exact_mod_cast (lt_of_not_ge hn).le

variable (u : sourceRing F S₀) (hu : u ≠ 0)

local notation "A" => sourcePrimeRowCharacter F hζ S₀ u hu
local notation "B" => sourcePrimeRowTwist F hζ S₀ u hu η
local notation "C" => sourcePrimeRowThirdPhase F hζ S₀ u hu η
local notation "e" => sourceElementExponents F S₀ u hu

include hM hcut in
theorem sourcePrimeBadCorrection_phase_norms (P : SourceExteriorPrime F S₀) :
    let χ := reflectionPrimeCharacters F hζ S₀ P
    ‖probeIdealGaussGamma F P.val χ 2‖ = 1 ∧
      ‖probeIdealGaussLocalVartheta F P.val χ (η.allCoefficient P.val.asIdeal)‖ = 1 ∧
      ‖(sourceResidualCharacterUnit F hζ S₀ u hu P : ℂ)‖ = 1 := by
  let χ := reflectionPrimeCharacters F hζ S₀ P
  refine ⟨probeBadIdealGaussGamma_norm_one F P.val χ
    (sourcePrimeCharacter_order F hζ S₀ P) 2 (by decide) (by decide), ?_,
    sourceResidualCharacter_norm_one F hζ S₀ u hu P⟩
  rw [probeBadIdealGaussLocalVartheta_norm F P.val χ
    (sourcePrimeCharacter_order F hζ S₀ P) (sourcePrimeResidue_char_ne_two F S₀ P)]
  exact principalAngular_value_norm η hM S hcut P

include hM hcut in
theorem sourcePrimeBadCorrection_norm_sub_one (P : SourceExteriorPrime F S₀)
    (hP : P ∈ (e).support) (q : ProbeCoordinates) (hq : q ∈ probeEulerDomain) :
    ‖sourcePrimeBadCorrection F hζ S₀ η u hu P q - 1‖ ≤
      36 * (Ideal.absNorm P.val.asIdeal : ℝ) ^ (-(1 / 4000 : ℝ)) := by
  have hj := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hP)
  obtain ⟨hγ, hν, hθ⟩ := sourcePrimeBadCorrection_phase_norms F hζ S₀ η hM hcut u hu P
  exact probeBadIdealSourceCorrection_regions F P.val (reflectionPrimeCharacters F hζ S₀ P)
    (sourcePrimeCharacter_order F hζ S₀ P) (sourcePrimeCharacter_minus_one F hζ S₀ P)
    (e P) hj _ _ _ hγ hν hθ
    (sourceExterior_norm_cutoff F S₀ (probePrimeCutoff_subset_principalAngularCutoff.trans hcut) P) q hq

include hM hcut in
theorem sourcePrimeBadCorrection_norm_le (P : SourceExteriorPrime F S₀)
    (hP : P ∈ (e).support) (q : ProbeCoordinates) (hq : q ∈ probeEulerDomain) :
    ‖sourcePrimeBadCorrection F hζ S₀ η u hu P q‖ ≤ 64 := by
  have h := sourcePrimeBadCorrection_norm_sub_one F hζ S₀ η hM hcut u hu P hP q hq
  have hQ : (1 : ℝ) ≤ Ideal.absNorm P.val.asIdeal := (probeIdealPrime_norm_gt_one F P.val).le
  have hδ : (Ideal.absNorm P.val.asIdeal : ℝ) ^ (-(1 / 4000 : ℝ)) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hQ
      (by norm_num : -(1 / 4000 : ℝ) ≤ 0)
  have hn := norm_add_le (sourcePrimeBadCorrection F hζ S₀ η u hu P q - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith

include hM hcut in
theorem sourcePrimeBadCorrection_differentiableOn (P : SourceExteriorPrime F S₀)
    (hP : P ∈ (e).support) :
    DifferentiableOn ℂ (sourcePrimeBadCorrection F hζ S₀ η u hu P) probeEulerOpenDomain := by
  have hj := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hP)
  obtain ⟨hγ, hν, hθ⟩ := sourcePrimeBadCorrection_phase_norms F hζ S₀ η hM hcut u hu P
  exact probeBadIdealSourceCorrection_differentiableOn_open F P.val (reflectionPrimeCharacters F hζ S₀ P)
    (sourcePrimeCharacter_order F hζ S₀ P) (sourcePrimeCharacter_minus_one F hζ S₀ P)
    (e P) hj _ _ _ hγ hν hθ
    (sourceExterior_norm_cutoff F S₀ (probePrimeCutoff_subset_principalAngularCutoff.trans hcut) P)

include hM hcut in
include hM hcut in
theorem sourceGlobalCorrection_differentiableOn :
    DifferentiableOn ℂ (sourceGlobalCorrection F hζ S₀ η u hu) probeEulerOpenDomain := by
  have ha := sourceExteriorValues_norm_le_one F S₀ A (sourcePrimeRowCharacter_norm_le_one F hζ S₀ u hu)
  have hb := sourceExteriorValues_norm_le_one F S₀ B (sourcePrimeRowTwist_norm_le_one F hζ S₀ u hu η)
  have hc := sourceExteriorValues_norm_le_one F S₀ C (sourcePrimeRowThirdPhase_norm_le_one F hζ S₀ u hu η)
  apply ((probeEulerProduct_differentiableOn F S
    (probePrimeCutoff_subset_principalAngularCutoff.trans hcut) _ _ _ ha hb hc).mono
      probeEulerOpenDomain_subset_interior).mul
  intro q hq
  have hProd (T : Finset (SourceExteriorPrime F S₀)) (hT : T ⊆ (e).support) :
      DifferentiableWithinAt ℂ
        (fun x : ProbeCoordinates => ∏ P ∈ T, sourcePrimeBadCorrection F hζ S₀ η u hu P x)
        probeEulerOpenDomain q := by
    induction T using Finset.induction_on with
    | empty =>
        simp only [Finset.prod_empty]
        exact differentiableWithinAt_const (1 : ℂ)
    | @insert P T hP ih =>
        simp only [Finset.prod_insert hP]
        exact (sourcePrimeBadCorrection_differentiableOn F hζ S₀ η hM hcut u hu P
          (hT (Finset.mem_insert_self P T)) q hq).mul (ih (fun _ hQ => hT (Finset.mem_insert_of_mem hQ)))
  exact hProd (e).support (fun _ h => h)

theorem sourceElementSupport_card_le_ideal :
    (e).support.card ≤ (HeckeIdealMobius.primeSupport F (sourcePrimeExponentIdeal F S₀ e)).card := by
  have hT : (e).support.map (sourceExteriorPrimeIdealEmbedding F S₀) ⊆
      HeckeIdealMobius.primeSupport F (sourcePrimeExponentIdeal F S₀ e) := by
    rw [HeckeIdealMobius.primeSupport, ← support_factorization, sourcePrimeExponentIdeal_factorization,
      Finsupp.support_embDomain]
  simpa only [Finset.card_map] using Finset.card_le_card hT

include hM hcut in
theorem sourceGlobalCorrection_uniform_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ (u : sourceRing F S₀) (hu : u ≠ 0) (q : ProbeCoordinates),
      q ∈ probeEulerDomain →
      ‖sourceGlobalCorrection F hζ S₀ η u hu q‖ ≤
        B₀ * (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) : ℝ) ^ ε := by
  obtain ⟨B₁, hB₁, hbound⟩ := exists_probe_primeSupport_product_bound F ε hε
  refine ⟨probeGoodProductUniformBound F * B₁, mul_pos (probeGoodProductUniformBound_pos F) hB₁, ?_⟩
  intro u₀ hu₀ q hq
  let e₀ := sourceElementExponents F S₀ u₀ hu₀
  let I := sourcePrimeExponentIdeal F S₀ e₀
  have h64 : (64 : ℝ) ^ (HeckeIdealMobius.primeSupport F I).card ≤ B₁ * (Ideal.absNorm I : ℝ) ^ ε := by
    simpa using hbound I (sourcePrimeExponentIdeal_ne_bot F S₀ e₀) (fun _ => (64 : ℂ)) (by norm_num)
  have hBad : ‖∏ P ∈ e₀.support, sourcePrimeBadCorrection F hζ S₀ η u₀ hu₀ P q‖ ≤
      B₁ * (sourcePrimeExponentNorm F S₀ e₀ : ℝ) ^ ε := by
    calc
      _ ≤ ∏ _P ∈ e₀.support, (64 : ℝ) := by
        rw [norm_prod]
        exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun P hP => sourcePrimeBadCorrection_norm_le F hζ S₀ η hM hcut u₀ hu₀ P hP q hq)
      _ = (64 : ℝ) ^ e₀.support.card := by simp
      _ ≤ (64 : ℝ) ^ (HeckeIdealMobius.primeSupport F I).card :=
        pow_le_pow_right₀ (by norm_num) (sourceElementSupport_card_le_ideal F S₀ u₀ hu₀)
      _ ≤ _ := by
        rw [← sourcePrimeExponentIdeal_norm F S₀ e₀]
        exact h64
  let a₀ := sourcePrimeRowCharacter F hζ S₀ u₀ hu₀
  let b₀ := sourcePrimeRowTwist F hζ S₀ u₀ hu₀ η
  let c₀ := sourcePrimeRowThirdPhase F hζ S₀ u₀ hu₀ η
  have hA := sourceExteriorValues_norm_le_one F S₀ a₀ (sourcePrimeRowCharacter_norm_le_one F hζ S₀ u₀ hu₀)
  have hB := sourceExteriorValues_norm_le_one F S₀ b₀ (sourcePrimeRowTwist_norm_le_one F hζ S₀ u₀ hu₀ η)
  have hC := sourceExteriorValues_norm_le_one F S₀ c₀ (sourcePrimeRowThirdPhase_norm_le_one F hζ S₀ u₀ hu₀ η)
  have hGood := probeEulerProduct_norm_le_uniform F S (probePrimeCutoff_subset_principalAngularCutoff.trans hcut)
    _ _ _ hA hB hC hq
  rw [sourceGlobalCorrection, norm_mul]
  exact (mul_le_mul hGood hBad (norm_nonneg _) (probeGoodProductUniformBound_pos F).le).trans_eq
    (by rw [mul_assoc])

end
end ArtinMatthews.SourceEulerAssembly
