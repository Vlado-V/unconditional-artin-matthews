module

public import ArtinMatthews.QuadraticHeckeSquarefreeNorm


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Set SourceEulerAssembly
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local notation "NZ" => {J : Ideal (𝓞 F) // J ≠ ⊥}

/-- The norm of the unique squarefree part cannot exceed the full ideal norm. -/
theorem quadraticHeckeSquarefreeNorm_le_absNorm (J : NZ) :
    quadraticHeckeSquarefreeNorm F J ≤ Ideal.absNorm J.val := by
  have hnorm := congrArg (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
    (sourceQuadraticIdealSquareParts_val F J)
  simp only [map_mul, map_pow] at hnorm
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr J.property))
  exact ⟨Ideal.absNorm (sourceQuadraticIdealSquareParts F J).2.val ^ 2, hnorm.symm⟩

theorem quadraticHeckeSquarefreeNorm_cast_le_absNorm (J : NZ) :
    (quadraticHeckeSquarefreeNorm F J : ℝ) ≤ (Ideal.absNorm J.val : ℝ) := by
  exact_mod_cast quadraticHeckeSquarefreeNorm_le_absNorm F J

theorem quadraticHeckeSquarefreeNorm_tail_subset (U : ℝ) :
    {J : NZ | U < (quadraticHeckeSquarefreeNorm F J : ℝ)} ⊆
      {J : NZ | U < (Ideal.absNorm J.val : ℝ)} := by
  intro J hJ
  exact hJ.trans_le (quadraticHeckeSquarefreeNorm_cast_le_absNorm F J)

/-- Every nonnegative squarefree-part tail is dominated by the full-norm tail. -/
theorem quadraticHeckeSquarefreeNorm_absolute_tail_le (f : NZ → ℝ)
    (hf : ∀ J, 0 ≤ f J) (hs : Summable f) (U : ℝ) :
    (∑' J : NZ, if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then f J else 0) ≤
      ∑' J : {J : NZ // U < (Ideal.absNorm J.val : ℝ)}, f J.val := by
  have hsum : (∑' J : {J : NZ // U < (Ideal.absNorm J.val : ℝ)}, f J.val) =
      ∑' J : NZ, if U < (Ideal.absNorm J.val : ℝ) then f J else 0 := by
    simpa only [Set.coe_ofPred, Set.indicator_apply, Set.mem_ofPred_eq] using
      (tsum_subtype {J : NZ | U < (Ideal.absNorm J.val : ℝ)} f)
  rw [hsum]
  have hsmall : Summable (fun J : NZ =>
      if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then f J else 0) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hs
    · intro J
      split_ifs
      · exact hf J
      · exact le_rfl
    · intro J
      split_ifs
      · exact le_rfl
      · exact hf J
  have hlarge : Summable (fun J : NZ =>
      if U < (Ideal.absNorm J.val : ℝ) then f J else 0) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hs
    · intro J
      split_ifs
      · exact hf J
      · exact le_rfl
    · intro J
      split_ifs
      · exact le_rfl
      · exact hf J
  apply hsmall.tsum_le_tsum _ hlarge
  intro J
  by_cases hJ : U < (quadraticHeckeSquarefreeNorm F J : ℝ)
  · have hnorm : U < (Ideal.absNorm J.val : ℝ) :=
      hJ.trans_le (quadraticHeckeSquarefreeNorm_cast_le_absNorm F J)
    simp only [hJ, hnorm, ite_true, le_refl]
  · simp only [hJ, ite_false]
    split_ifs <;> first | exact hf J | exact le_rfl

/-- Taking the norm of a masked complex tail preserves the same domination. -/
theorem quadraticHeckeSquarefreeNorm_tail_norm_le (f : NZ → ℂ)
    (hs : Summable (fun J => ‖f J‖)) (U : ℝ) :
    ‖∑' J : NZ, if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then f J else 0‖ ≤
      ∑' J : {J : NZ // U < (Ideal.absNorm J.val : ℝ)}, ‖f J.val‖ := by
  have hmasked : Summable (fun J : NZ =>
      ‖if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then f J else 0‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hs
    intro J
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (f J)
  calc
    _ ≤ ∑' J : NZ, ‖if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then f J else 0‖ :=
      norm_tsum_le_tsum_norm hmasked
    _ = ∑' J : NZ, if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then ‖f J‖ else 0 := by
      apply tsum_congr
      intro J
      split_ifs <;> simp
    _ ≤ _ := quadraticHeckeSquarefreeNorm_absolute_tail_le F
      (fun J => ‖f J‖) (fun _ => norm_nonneg _) hs U

end
end ArtinMatthews
