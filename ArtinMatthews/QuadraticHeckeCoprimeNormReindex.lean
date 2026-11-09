module

public import ArtinMatthews.QuadraticHeckeNormCoprime
public import ArtinMatthews.QuadraticHeckePrincipalNormSeries


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Set MeasureTheory VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local notation "J₀" => {J : Ideal (𝓞 F) // J ≠ ⊥}

omit [NumberField F] in
private theorem nonzeroIdeal_tsum (f : Ideal (𝓞 F) → ℂ) (hf : f ⊥ = 0) :
    (∑' J : J₀, f J.val) = ∑' J : Ideal (𝓞 F), f J := by
  apply tsum_subtype_eq_of_support_subset
  intro J hJ hzero
  exact hJ (hzero ▸ hf)

/-- Coprimality in a genuine ideal norm sum becomes a finite sum of
unrestricted sums at the exact rescaled norm parameter. -/
theorem quadraticHeckeCoprimeNorm_reindex (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (v : ℝ → ℂ) {X : ℝ} (hX : 0 < X)
    (hv : Summable (fun J : J₀ => ‖v ((Ideal.absNorm J.val : ℝ) / X)‖)) :
    (∑' J : J₀, if IsCoprime J.val m then v ((Ideal.absNorm J.val : ℝ) / X) else 0) =
      ∑ d ∈ HeckeIdealMobius.divisors F m, (moebius d : ℂ) *
        ∑' J : J₀, v ((Ideal.absNorm J.val : ℝ) / (X / (Ideal.absNorm d : ℝ))) := by
  let f : Ideal (𝓞 F) → ℂ := fun J => if J = ⊥ then 0 else v ((Ideal.absNorm J : ℝ) / X)
  have hf₀ : f ⊥ = 0 := by simp [f]
  have hfsub : Summable (fun J : J₀ => f J.val) :=
    hv.of_norm.congr (fun J => by simp [f, J.property])
  have hf : Summable f := by
    have h := (summable_subtype_iff_indicator (f := f)
      (s := {J : Ideal (𝓞 F) | J ≠ ⊥})).mp hfsub
    apply h.congr
    intro J
    by_cases hJ : J = ⊥ <;> simp [Set.indicator, hJ, f]
  have hleft :
      (∑' J : J₀, if IsCoprime J.val m then v ((Ideal.absNorm J.val : ℝ) / X) else 0) =
        ∑' J : Ideal (𝓞 F), if IsCoprime J m then f J else 0 := by
    rw [← nonzeroIdeal_tsum F (fun J => if IsCoprime J m then f J else 0)
      (by simp [hf₀])]
    apply tsum_congr
    intro J
    simp [f, J.property]
  rw [hleft, quadraticHeckeNorm_coprime_tsum F m hm f hf hf₀]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' : d ≠ ⊥ := by
    intro hd0
    have hdvd := (HeckeIdealMobius.mem_divisors F hm).1 hd
    obtain ⟨J, hJ⟩ := hdvd
    exact hm (by rw [hJ, hd0, Ideal.bot_mul])
  have hdn : (Ideal.absNorm d : ℝ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hd'
  congr 1
  rw [← nonzeroIdeal_tsum F (fun J => f (d * J)) (by simp [f])]
  apply tsum_congr
  intro J
  have hdJ : d * J.val ≠ ⊥ := mul_ne_zero hd' J.property
  simp only [f, ite_eq_right hdJ, map_mul, Nat.cast_mul]
  congr 1
  field_simp [hX.ne', hdn]

end
end ArtinMatthews
