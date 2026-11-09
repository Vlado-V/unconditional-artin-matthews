module

public import ArtinMatthews.SourceReflectionDirichlet


set_option backward.privateInPublic true
@[expose] public section

/-! The literal frozen, cube and column weights give the summable
absolute coefficient majorant for reflection. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField ENNReal
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "Prime" => SourceExteriorPrime F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "N" => sourcePrimeExponentNorm F S₀

theorem sourceReflectionTermIndex_countable (f : Finset Prime) :
    Countable (SourceReflectionTermIndex F S₀ f) := by
  let w (e : E) := (N e : ℝ)^(-2 : ℝ)
  have hw : Summable w := sourcePrimeExponentNorm_summable F S₀ (σ := 2) (by norm_num)
  have hs : Function.support w = Set.univ := Set.eq_univ_of_forall fun e =>
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ e)) _).ne'
  let _ : Countable E := Set.countable_univ_iff.mp (hs ▸ hw.countable_support)
  unfold SourceReflectionTermIndex SourceReflectionFrozenNumerator ReflectionSquarefreeExponents
  infer_instance

theorem sourceReflectionDirichletTerm_zero (f : Finset Prime)
    (i : SourceReflectionTermIndex F S₀ f) :
    sourceReflectionDirichletTerm F S₀ f 0 i =
      sourceReflectionFrozenWeight F S₀ f i.1.val /
        (Real.sqrt (N i.2.2.val : ℝ) * (N i.2.1 : ℝ)) := by
  let Q : ℝ := N i.2.2.val
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have hp : Q^(-1/2 : ℝ) = (Real.sqrt Q)⁻¹ := by
    rw [show (-1/2 : ℝ) = -(1/2) by ring, Real.rpow_neg hQ, Real.sqrt_eq_rpow]
  rw [sourceReflectionDirichletTerm, neg_zero, Real.rpow_zero, mul_one, hp]
  have hQ₀ : 0 < Real.sqrt Q := Real.sqrt_pos.2
    (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ _))
  have hn : (0 : ℝ) < N i.2.1 := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ _)
  change _ = sourceReflectionFrozenWeight F S₀ f i.1.val / (Real.sqrt Q * (N i.2.1 : ℝ))
  field_simp [hQ₀.ne', hn.ne']

theorem sourceReflectionDirichletTerm_mul_length (f : Finset Prime) (σ : ℝ)
    (i : SourceReflectionTermIndex F S₀ f) :
    sourceReflectionDirichletTerm F S₀ f 0 i *
      sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val ^ (-σ) =
      sourceReflectionDirichletTerm F S₀ f σ i := by
  simp only [sourceReflectionDirichletTerm, neg_zero, Real.rpow_zero, mul_one]

theorem sourceReflectionCoefficient_summable (f : Finset Prime) {σ : ℝ} (hσ : 1/2 < σ)
    (a : SourceReflectionTermIndex F S₀ f → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ sourceReflectionDirichletTerm F S₀ f 0 i) :
    Summable (fun i => ‖a i‖ * sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val ^ (-σ)) := by
  have hL (i : SourceReflectionTermIndex F S₀ f) :
      0 ≤ sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val :=
    zero_le_one.trans (sourceReflectionTermLength_one_le F S₀ _ _ _)
  apply Summable.of_nonneg_of_le
    (fun i => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hL i) _)) _
    (sourceReflectionDirichlet_hasSum F S₀ f hσ).summable
  intro i
  rw [← sourceReflectionDirichletTerm_mul_length]
  exact mul_le_mul_of_nonneg_right (ha i) (Real.rpow_nonneg (hL i) _)

end
end ArtinMatthews.SourceEulerAssembly
