module

public import ArtinMatthews.VaryingKummerAnalyticIdealFrequencyLabels


set_option backward.privateInPublic true
@[expose] public section

/-! Distinct actual ideal/residue labels give separated frequencies, including
every translation by the trace-dual lattice of the ring of integers. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- A nonzero integral modulus together with a unit of its residue ring. -/
abbrev IdealFrequencyLabel :=
  Σ M : {I : Ideal (𝓞 K) // I ≠ ⊥}, ((𝓞 K) ⧸ M.val)ˣ

def idealFrequencyLabelValue (ℓ : IdealFrequencyLabel K) : K :=
  idealFrequencyValue K ℓ.1.val ℓ.1.property ℓ.2

theorem idealFrequencyLabelValue_mem_dual (ℓ : IdealFrequencyLabel K) :
    idealFrequencyLabelValue K ℓ ∈
      FractionalIdeal.dual ℤ ℚ (ℓ.1.val : FractionalIdeal (𝓞 K)⁰ K) :=
  idealFrequencyValue_mem_dual K ℓ.1.val ℓ.1.property ℓ.2

theorem idealFrequencyLabel_eq_of_sub_mem_dual (ℓ ℓ' : IdealFrequencyLabel K)
    (h : idealFrequencyLabelValue K ℓ - idealFrequencyLabelValue K ℓ' ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) : ℓ = ℓ' := by
  rcases ℓ with ⟨⟨M, hM⟩, u⟩
  rcases ℓ' with ⟨⟨N, hN⟩, v⟩
  have hMN := idealFrequencyValue_modulus_eq_of_sub_mem_dual K M N hM hN u v h
  cases hMN
  have huv := idealFrequencyValue_injective_mod_dual K M hM u v h
  subst v
  rfl

theorem idealFrequencyLabel_character_injective :
    Function.Injective (fun ℓ : IdealFrequencyLabel K =>
      fieldTraceAddChar K (idealFrequencyLabelValue K ℓ)) := by
  intro ℓ ℓ' h
  exact idealFrequencyLabel_eq_of_sub_mem_dual K ℓ ℓ'
    ((fieldTraceAddChar_eq_iff_sub_mem_dual K _ _).mp h)

theorem idealFrequencyLabel_difference_ne_zero
    {ℓ ℓ' : IdealFrequencyLabel K} (hne : ℓ ≠ ℓ') {r : K}
    (hr : r ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    idealFrequencyLabelValue K ℓ - idealFrequencyLabelValue K ℓ' + r ≠ 0 := by
  intro hz
  apply hne
  apply idealFrequencyLabel_eq_of_sub_mem_dual K
  have he : idealFrequencyLabelValue K ℓ - idealFrequencyLabelValue K ℓ' = -r :=
    eq_neg_of_add_eq_zero_left hz
  rw [he]
  exact (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)).val.neg_mem hr

theorem idealFrequencyLabel_mixed_separation
    {ℓ ℓ' : IdealFrequencyLabel K} (hne : ℓ ≠ ℓ') {r : K}
    (hr : r ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    1 / (|(NumberField.discr K : ℝ)| *
      (Ideal.absNorm ℓ.1.val : ℝ) * (Ideal.absNorm ℓ'.1.val : ℝ)) ≤
      ‖mixedEmbedding K
        (idealFrequencyLabelValue K ℓ - idealFrequencyLabelValue K ℓ' + r)‖ ^
        Module.finrank ℚ K :=
  idealFrequency_mixed_separation K ℓ.1.val ℓ'.1.val ℓ.1.property ℓ'.1.property
    (idealFrequencyLabelValue_mem_dual K ℓ) (idealFrequencyLabelValue_mem_dual K ℓ')
    hr (idealFrequencyLabel_difference_ne_zero K hne hr)

theorem idealFrequencyLabel_mixed_separation_norm_cutoff
    {ℓ ℓ' : IdealFrequencyLabel K} (hne : ℓ ≠ ℓ') {r : K}
    (hr : r ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) {U : ℝ}
    (hℓU : (Ideal.absNorm ℓ.1.val : ℝ) ≤ U)
    (hℓ'U : (Ideal.absNorm ℓ'.1.val : ℝ) ≤ U) :
    1 / (|(NumberField.discr K : ℝ)| * U ^ 2) ≤
      ‖mixedEmbedding K
        (idealFrequencyLabelValue K ℓ - idealFrequencyLabelValue K ℓ' + r)‖ ^
        Module.finrank ℚ K :=
  idealFrequency_mixed_separation_norm_cutoff K ℓ.1.val ℓ'.1.val
    ℓ.1.property ℓ'.1.property (idealFrequencyLabelValue_mem_dual K ℓ)
    (idealFrequencyLabelValue_mem_dual K ℓ') hr
    (idealFrequencyLabel_difference_ne_zero K hne hr) hℓU hℓ'U

end
end ArtinMatthews.VaryingKummerAnalytic
