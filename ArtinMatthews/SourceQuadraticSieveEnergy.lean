module

public import ArtinMatthews.SourceQuadraticSieveInitial
public import ArtinMatthews.QuadraticHeckeSieveBootstrap


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "E" => ReflectionSquarefreeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "a" => sourcePrimeExponentGenerator F hζ S₀

def sourceQuadraticSieveRowEnergy (rows cols : Finset E) (c : E → ℂ) : ℝ :=
  ∑ e ∈ rows, ‖∑ f ∈ cols, c f * reflectionExponentResidueValue F hζ S₀ f.val (a e.val) ^ 3‖ ^ 2

/-- Admissible sharp constants for the actual exterior family on a row dyad
and column norm ball. Zero extension allows arbitrary row and column subsets. -/
def SourceQuadraticDyadicAdmissible (M N B : ℝ) : Prop :=
  0 ≤ B ∧ ∀ (rows cols : Finset E),
    (∀ e ∈ rows, M ≤ (q e.val : ℝ) ∧ (q e.val : ℝ) ≤ 2 * M) →
    (∀ e ∈ cols, (q e.val : ℝ) ≤ N) → ∀ c : E → ℂ,
    sourceQuadraticSieveRowEnergy F S₀ hζ rows cols c ≤ B * ∑ f ∈ cols, ‖c f‖ ^ 2

def sourceQuadraticDyadicEnergy (M N : ℝ) : ℝ :=
  sInf {B : ℝ | SourceQuadraticDyadicAdmissible F S₀ hζ M N B}

theorem sourceQuadraticDyadicEnergy_le {M N B : ℝ}
    (h : SourceQuadraticDyadicAdmissible F S₀ hζ M N B) :
    sourceQuadraticDyadicEnergy F S₀ hζ M N ≤ B :=
  csInf_le ⟨0, fun _ hb => hb.1⟩ h

variable [IsTotallyComplex F]

theorem exists_sourceQuadraticDyadicAdmissible (htrace : traceBadPlaces F ⊆ S)
    {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) :
    ∃ B : ℝ, SourceQuadraticDyadicAdmissible F S₀ hζ M N B := by
  obtain ⟨C, hC, h⟩ := exists_sourceQuadraticSieve_initial F S₀ hζ htrace
  exact ⟨C * (M + N ^ 2), by positivity, h M N hM hN⟩

theorem sourceQuadraticDyadicEnergy_admissible (htrace : traceBadPlaces F ⊆ S)
    {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) :
    SourceQuadraticDyadicAdmissible F S₀ hζ M N (sourceQuadraticDyadicEnergy F S₀ hζ M N) := by
  obtain ⟨B, hB⟩ := exists_sourceQuadraticDyadicAdmissible F S₀ hζ htrace hM hN
  have hne : {B : ℝ | SourceQuadraticDyadicAdmissible F S₀ hζ M N B}.Nonempty := ⟨B, hB⟩
  refine ⟨le_csInf hne (fun _ h => h.1), ?_⟩
  intro rows cols hr hc c
  let m : ℝ := ∑ f ∈ cols, ‖c f‖ ^ 2
  have hm : 0 ≤ m := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases eq_or_lt_of_le hm with hm | hm
  · have h := hB.2 rows cols hr hc c
    change _ ≤ B * m at h
    change _ ≤ sourceQuadraticDyadicEnergy F S₀ hζ M N * m
    rw [← hm, mul_zero] at h ⊢
    exact h
  · change _ ≤ sourceQuadraticDyadicEnergy F S₀ hζ M N * m
    apply (div_le_iff₀ hm).mp
    exact le_csInf hne (fun D hd => (div_le_iff₀ hm).mpr (hd.2 rows cols hr hc c))

theorem sourceQuadraticDyadicEnergy_exponent_two (htrace : traceBadPlaces F ⊆ S) :
    QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) 2 := by
  obtain ⟨C, hC, h⟩ := exists_sourceQuadraticSieve_initial F S₀ hζ htrace
  intro ε hε
  refine ⟨C, hC, ?_⟩
  intro M N hM hN
  have hB : SourceQuadraticDyadicAdmissible F S₀ hζ M N (C * (M + N ^ 2)) :=
    ⟨by positivity, h M N hM hN⟩
  have hMN : 1 ≤ M * N := one_le_mul_of_one_le_of_one_le hM hN
  calc
    _ ≤ C * (M + N ^ 2) := sourceQuadraticDyadicEnergy_le F S₀ hζ hB
    _ ≤ C * (M * N) ^ ε * (M + N ^ (2 : ℝ)) := by
      rw [Real.rpow_two]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact le_mul_of_one_le_right hC.le (Real.one_le_rpow hMN hε.le)

end
end ArtinMatthews.SourceEulerAssembly
