module

public import ArtinMatthews.SourceReflectionPowerfulCount
public import ArtinMatthews.SourcePrimeExponentProducts


set_option backward.privateInPublic true
@[expose] public section

/-! The unique powerful/simple splitting and ideal counts on the exterior
coordinates of the actual source. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

def sourceReflectionExteriorPrimeEmbedding : SourceExteriorPrime F S₀ ↪ ProbePrime F :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem sourceReflectionFullExteriorIdeal (e : E) :
    sourceFullExponentIdeal F (e.embDomain (sourceReflectionExteriorPrimeEmbedding F S₀)) =
      sourcePrimeExponentIdeal F S₀ e :=
  Finsupp.prod_embDomain

theorem sourceReflectionExteriorIdeal_powerful (e : E) (he : sourceReflectionIsPowerful e) :
    sourceReflectionPowerfulIdeal F (sourcePrimeExponentIdeal F S₀ e) := by
  refine ⟨sourcePrimeExponentIdeal_ne_bot F S₀ e, ?_⟩
  rw [← sourceReflectionFullExteriorIdeal F S₀ e]
  change sourceReflectionIsPowerful
    ((sourceFullExponentIdealEquiv F).symm
      ((sourceFullExponentIdealEquiv F) (e.embDomain (sourceReflectionExteriorPrimeEmbedding F S₀))))
  rw [Equiv.symm_apply_apply]
  intro P
  by_cases hp : P ∈ Set.range (sourceReflectionExteriorPrimeEmbedding F S₀)
  · obtain ⟨p, rfl⟩ := hp
    simpa only [Finsupp.embDomain_apply_self] using he p
  · rw [Finsupp.embDomain_of_notMem_range _ _ _ hp]
    decide

theorem sourceReflectionExteriorIdeal_squarefree (e : E) :
    Squarefree (sourcePrimeExponentIdeal F S₀ e) ↔ sourceReflectionIsSquarefree e := by
  rw [← sourceReflectionFullExteriorIdeal F S₀ e, sourceFullExponentIdeal_squarefree_iff]
  constructor
  · intro h P
    simpa only [Finsupp.embDomain_apply_self] using h (sourceReflectionExteriorPrimeEmbedding F S₀ P)
  · intro h P
    by_cases hp : P ∈ Set.range (sourceReflectionExteriorPrimeEmbedding F S₀)
    · obtain ⟨p, rfl⟩ := hp
      simpa only [Finsupp.embDomain_apply_self] using h p
    · rw [Finsupp.embDomain_of_notMem_range _ _ _ hp]
      decide

theorem sourceReflectionExteriorRow_product (e : E) :
    sourcePrimeExponentIdeal F S₀ (sourceReflectionPowerfulPart e) *
      sourcePrimeExponentIdeal F S₀ (sourceReflectionSimplePart e) = sourcePrimeExponentIdeal F S₀ e := by
  rw [← sourcePrimeExponentIdeal_add, sourceReflectionPowerfulSimple_add]

theorem sourceReflectionExteriorRow_norm (e : E) :
    q (sourceReflectionPowerfulPart e) * q (sourceReflectionSimplePart e) = q e := by
  rw [← sourcePrimeExponentNorm_add, sourceReflectionPowerfulSimple_add]

theorem sourceReflectionExteriorNorm_mono {e f : E} (hef : ∀ P, e P ≤ f P) : q e ≤ q f := by
  have hsupport : e.support ⊆ f.support := by
    intro P hP
    apply Finsupp.mem_support_iff.mpr
    exact (ne_of_gt ((Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hP)).trans_le (hef P)))
  unfold sourcePrimeExponentNorm
  rw [Finsupp.prod_of_support_subset e hsupport _ (fun _ _ => pow_zero _)]
  apply Finset.prod_le_prod
  intro P _
  exact pow_le_pow_right₀ ((NumberField.HeightOneSpectrum.one_lt_absNorm P.val).le) (hef P)

theorem sourceReflectionExteriorNorm_nsmul (e : E) (n : ℕ) : q (n • e) = q e ^ n := by
  induction n with
  | zero => rw [zero_nsmul, sourcePrimeExponentNorm_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, sourcePrimeExponentNorm_add, ih, pow_succ]

/-- Squarefree active products can use only primes in the powerful part.
In particular their squared norms do not exceed the powerful row norm. -/
theorem sourceReflectionActiveNorm_sq_le {h f : E}
    (hh : sourceReflectionIsPowerful h) (hf : sourceReflectionIsSquarefree f)
    (hsub : f.support ⊆ h.support) : (q f : ℝ) ^ 2 ≤ (q h : ℝ) := by
  have hb : q (2 • f) ≤ q h := by
    apply sourceReflectionExteriorNorm_mono F S₀
    intro P
    simp only [Finsupp.smul_apply, Nat.nsmul_eq_mul]
    by_cases hp : P ∈ f.support
    · have hP := Finsupp.mem_support_iff.mp (hsub hp)
      have := hf P
      have := hh P
      omega
    · have := Finsupp.notMem_support_iff.mp hp
      omega
  rw [sourceReflectionExteriorNorm_nsmul] at hb
  exact_mod_cast hb

theorem exists_sourceReflectionExteriorCard_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 1 ≤ X → ∀ A : Finset E,
      (∀ e ∈ A, (q e : ℝ) ≤ X) → (A.card : ℝ) ≤ C * X := by
  obtain ⟨C, hC, hcount⟩ := exists_sourceReflectionIdealCard_le F
  refine ⟨C, hC, fun X hX A hA => ?_⟩
  have h := hcount X hX (A.image (sourcePrimeExponentIdeal F S₀)) (by
    intro I hI
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hI
    rw [sourcePrimeExponentIdeal_norm]
    exact hA e he)
  simpa only [Finset.card_image_of_injective _ (sourcePrimeExponentIdeal_injective F S₀)] using h

theorem exists_sourceReflectionExteriorPowerfulCard_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 1 ≤ X → ∀ A : Finset E,
      (∀ e ∈ A, sourceReflectionIsPowerful e ∧ (q e : ℝ) ≤ X) →
      (A.card : ℝ) ≤ C * Real.sqrt X := by
  obtain ⟨C, hC, hcount⟩ := exists_sourceReflectionPowerfulIdealCard_le F
  refine ⟨C, hC, fun X hX A hA => ?_⟩
  have h := hcount X hX (A.image (sourcePrimeExponentIdeal F S₀)) (by
    intro I hI
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨sourceReflectionExteriorIdeal_powerful F S₀ e (hA e he).1,
      by rw [sourcePrimeExponentIdeal_norm]; exact (hA e he).2⟩)
  simpa only [Finset.card_image_of_injective _ (sourcePrimeExponentIdeal_injective F S₀)] using h

end
end ArtinMatthews.SourceEulerAssembly
