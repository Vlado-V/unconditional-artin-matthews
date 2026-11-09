module

public import ArtinMatthews.SourceJacquetAdditiveTranslation
public import ArtinMatthews.StandardLocalBallFourier


set_option backward.privateInPublic true
@[expose] public section

/-! A single nontrivial character shift cancels a translation-invariant
outer region for the actual self-dual measure at every finite place. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical Filter
open scoped NumberField SourcePhysical Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "B" => sourceLocalBall K P
local notation "μ₀" => sourceLocalSelfDual K P
local notation "ψ₀" => localFiniteCharacter K P

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem sourceKPJacquetSelfDual_translate_measurePreserving (S : Set L) (a : L)
    (hS : ∀ x : L, x + a ∈ S ↔ x ∈ S) :
    MeasurePreserving (fun x : L => x + a) ((μ₀).restrict S) ((μ₀).restrict S) := by
  let : (μ₀).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  let e := MeasurableEquiv.addRight a
  have he : MeasurePreserving e μ₀ μ₀ := measurePreserving_add_right μ₀ a
  have hset : e ⁻¹' S = S := Set.ext hS
  have h := he.restrict_preimage_emb e.measurableEmbedding S
  rw [hset] at h
  exact h

theorem sourceKPJacquetSelfDual_translate_integrable_iff (S : Set L) (a : L)
    (hS : ∀ x : L, x + a ∈ S ↔ x ∈ S) (F : L → V) :
    IntegrableOn (fun x => F (x + a)) S μ₀ ↔ IntegrableOn F S μ₀ :=
  (sourceKPJacquetSelfDual_translate_measurePreserving K P S a hS).integrable_comp_emb (g := F)
    (MeasurableEquiv.addRight a).measurableEmbedding

theorem sourceKPJacquetSelfDual_translate_integral (S : Set L) (a : L)
    (hS : ∀ x : L, x + a ∈ S ↔ x ∈ S) (F : L → V) :
    (∫ x in S, F (x + a) ∂μ₀) = ∫ x in S, F x ∂μ₀ :=
  (sourceKPJacquetSelfDual_translate_measurePreserving K P S a hS).integral_comp
    (MeasurableEquiv.addRight a).measurableEmbedding F

variable [NormedSpace ℂ V] [SMulCommClass ℝ ℂ V]

theorem sourceKPJacquetSelfDual_integral_zero_of_phase (S : Set L) (hS : MeasurableSet S)
    (a : L) (hInv : ∀ x : L, x + a ∈ S ↔ x ∈ S) (F : L → V) (c : ℂ) (hc : c ≠ 1)
    (hphase : ∀ x ∈ S, F (x + a) = c • F x) : (∫ x in S, F x ∂μ₀) = 0 := by
  have he : (∫ x in S, F x ∂μ₀) = c • ∫ x in S, F x ∂μ₀ := by
    calc
      _ = ∫ x in S, F (x + a) ∂μ₀ :=
        (sourceKPJacquetSelfDual_translate_integral K P S a hInv F).symm
      _ = ∫ x in S, c • F x ∂μ₀ := setIntegral_congr_fun hS hphase
      _ = _ := integral_smul c F
  have hz : (c - 1) • (∫ x in S, F x ∂μ₀) = 0 := by
    rw [sub_smul, one_smul, ← he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)

theorem sourceKPJacquetSelfDual_ball_mono {R S : ℤ} (hRS : R ≤ S) : B R ⊆ B S :=
  fun _ hx => hx.trans (WithZero.exp_le_exp.mpr hRS)

theorem sourceKPJacquetSelfDual_fixed_shift_exists : ∃ a : L, ψ₀ (-a) ≠ 1 := by
  obtain ⟨a, _, ha⟩ := sourceLocalCharacter_next_ball_nontrivial K P
  refine ⟨a, fun h => ha ?_⟩
  rw [AddChar.map_neg_eq_inv] at h
  simpa only [inv_inv, inv_one] using congrArg Inv.inv h

theorem sourceKPJacquetSelfDual_ball_character_zero (R : ℤ) (a : L)
    (ha : a ∈ B R) (hc : ψ₀ (-a) ≠ 1) : (∫ x in B R, ψ₀ (-x) ∂μ₀) = 0 := by
  apply sourceKPJacquetSelfDual_integral_zero_of_phase K P (B R)
    (sourceLocalBall_isOpen K P R).measurableSet a
    (fun x => sourceJacquetBall_translate_mem_iff K P R a x ha) _ (ψ₀ (-a)) hc
  intro x _
  rw [neg_add, AddChar.map_add_eq_mul, smul_eq_mul, mul_comm]

theorem sourceKPJacquetSelfDual_truncation_stabilizes (F : L → V) (R₀ : ℕ) (a : L)
    (ha : a ∈ B (R₀ : ℤ)) (c : ℂ) (hc : c ≠ 1)
    (hi : ∀ R : ℕ, IntegrableOn F (B (R : ℤ)) μ₀)
    (hshift : ∀ x ∉ B (R₀ : ℤ), F (x + a) = c • F x) :
    ∀ R ≥ R₀, (∫ x in B (R : ℤ), F x ∂μ₀) = ∫ x in B (R₀ : ℤ), F x ∂μ₀ := by
  intro R hR
  have hsub : B (R₀ : ℤ) ⊆ B (R : ℤ) :=
    sourceKPJacquetSelfDual_ball_mono K P (by exact_mod_cast hR)
  let S := B (R : ℤ) \ B (R₀ : ℤ)
  have hs : MeasurableSet S := (sourceLocalBall_isOpen K P _).measurableSet.diff
    (sourceLocalBall_isOpen K P _).measurableSet
  have hInv (x : L) : x + a ∈ S ↔ x ∈ S := by
    simp only [S, Set.mem_sdiff,
      sourceJacquetBall_translate_mem_iff K P (R : ℤ) a x (hsub ha),
      sourceJacquetBall_translate_mem_iff K P (R₀ : ℤ) a x ha]
  have hz : (∫ x in S, F x ∂μ₀) = 0 :=
    sourceKPJacquetSelfDual_integral_zero_of_phase K P S hs a hInv F c hc
      (fun x hx => hshift x hx.2)
  have he := setIntegral_sdiff (sourceLocalBall_isOpen K P (R₀ : ℤ)).measurableSet (hi R) hsub
  exact sub_eq_zero.mp (he.symm.trans hz)

end
end ArtinMatthews
