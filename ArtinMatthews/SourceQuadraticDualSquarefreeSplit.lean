module

public import ArtinMatthews.SourceQuadraticBlockPoissonExpansion
public import ArtinMatthews.QuadraticHeckeRayDualTail
public import ArtinMatthews.QuadraticHeckeSquarefreeNorm


set_option backward.privateInPublic true
@[expose] public section

/-! Exact truncation of the actual dual ideal sum by its squarefree part.
The cutoff is arbitrary and the complementary tail remains explicit. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField Set VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "J₀" => {J : Ideal (𝓞 F) // J ≠ ⊥}
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "D" => quadraticHeckeDualProfile (quadraticHeckeFieldScale F)
  (InfinitePlace.nrComplexPlaces F) sourceQuadraticBlockProfile
local notation:max "Q" e:max => (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ)

omit [IsTotallyComplex F] in
theorem sourceQuadraticDual_conductorNorm_pos (e : E) : 0 < Q e := by
  exact_mod_cast Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (sourceQuadraticConductor_ne_bot F S₀ hζ e))

def sourceQuadraticDualSummand (e : E) (X : ℝ) (J : J₀) : ℂ :=
  (Ψ e).allCoefficient J.val * D ((Ideal.absNorm J.val : ℝ)*X/Q e)

def sourceQuadraticDualTruncated (e : E) (X U : ℝ) : ℂ :=
  ∑' J : J₀, if (quadraticHeckeSquarefreeNorm F J : ℝ) ≤ U then
    sourceQuadraticDualSummand F S₀ hζ e X J else 0

def sourceQuadraticDualSquarefreeTail (e : E) (X U : ℝ) : ℂ :=
  ∑' J : J₀, if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then
    sourceQuadraticDualSummand F S₀ hζ e X J else 0

/-- Absolute summability is supplied by the actual dual-profile theorem. -/
theorem sourceQuadraticDualSummand_norm_summable (e : E) {X : ℝ} (hX : 0 < X) :
    Summable (fun J : J₀ => ‖sourceQuadraticDualSummand F S₀ hζ e X J‖) := by
  have h := quadraticHeckeRayDualTerm_norm_summable F (Ψ e)
    (quadraticHeckeFieldScale F) (InfinitePlace.nrComplexPlaces F) sourceQuadraticBlockProfile
    sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
    sourceQuadraticBlockProfile_smooth (div_pos hX (sourceQuadraticDual_conductorNorm_pos F S₀ hζ e))
  apply h.congr
  intro J
  congr 1
  unfold quadraticHeckeRayDualTerm sourceQuadraticDualSummand
  congr 1
  congr 1
  ring

theorem sourceQuadraticDual_full_eq_truncated_add_tail (e : E) {X : ℝ}
    (hX : 0 < X) (U : ℝ) :
    (∑' J : J₀, sourceQuadraticDualSummand F S₀ hζ e X J) =
      sourceQuadraticDualTruncated F S₀ hζ e X U +
        sourceQuadraticDualSquarefreeTail F S₀ hζ e X U := by
  have hf := (sourceQuadraticDualSummand_norm_summable F S₀ hζ e hX).of_norm
  have hlo : Summable (fun J : J₀ => if (quadraticHeckeSquarefreeNorm F J : ℝ) ≤ U then
      sourceQuadraticDualSummand F S₀ hζ e X J else 0) :=
    hf.indicator {J : J₀ | (quadraticHeckeSquarefreeNorm F J : ℝ) ≤ U}
  have hhi : Summable (fun J : J₀ => if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then
      sourceQuadraticDualSummand F S₀ hζ e X J else 0) :=
    hf.indicator {J : J₀ | U < (quadraticHeckeSquarefreeNorm F J : ℝ)}
  change _ = (∑' J : J₀, if (quadraticHeckeSquarefreeNorm F J : ℝ) ≤ U then
      sourceQuadraticDualSummand F S₀ hζ e X J else 0) +
    ∑' J : J₀, if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then
      sourceQuadraticDualSummand F S₀ hζ e X J else 0
  rw [← hlo.tsum_add hhi]
  apply tsum_congr
  intro J
  by_cases hJ : (quadraticHeckeSquarefreeNorm F J : ℝ) ≤ U <;> simp [hJ]

/-- The truncation retains the source character on its squarefree ideal
and the conductor mask on its square ideal. -/
theorem sourceQuadraticDualTruncated_eq_squarefree (e : E) {X : ℝ}
    (hX : 0 < X) (U : ℝ) :
    sourceQuadraticDualTruncated F S₀ hζ e X U =
      ∑' a : {J : Ideal (𝓞 F) // Squarefree J},
        if (Ideal.absNorm a.val : ℝ) ≤ U then
          (Ψ e).allCoefficient a.val * ∑' b : J₀,
            if IsCoprime b.val (sourceQuadraticConductor F S₀ hζ e) then
              D ((Ideal.absNorm a.val : ℝ)*(Ideal.absNorm b.val : ℝ)^2/(Q e/X)) else 0
        else 0 := by
  have hquad (J : J₀) (hJ : IsCoprime J.val (sourceQuadraticConductor F S₀ hζ e)) :
      (Ψ e).allCoefficient J.val ^ 2 = 1 := by
    unfold EvenIdealRayCharacter.allCoefficient
    rw [dite_eq_left J.property, ite_eq_left hJ]
    exact congrArg Units.val (sourceQuadraticRayCharacter_sq F S₀ hζ e _)
  have habs : Summable (fun J : J₀ => ‖(Ψ e).allCoefficient J.val *
      D ((Ideal.absNorm J.val : ℝ)/(Q e/X))‖) := by
    simpa only [sourceQuadraticDualSummand, div_div_eq_mul_div] using
      sourceQuadraticDualSummand_norm_summable F S₀ hζ e hX
  have h := quadraticHeckeSquarefreeNorm_tsum F (Ψ e) hquad (1 : Ideal (𝓞 F)) U (Q e/X) D habs
  simpa only [sourceQuadraticDualTruncated, sourceQuadraticDualSummand,
    isCoprime_one_right, true_and, div_div_eq_mul_div] using h

end
end ArtinMatthews.SourceEulerAssembly
