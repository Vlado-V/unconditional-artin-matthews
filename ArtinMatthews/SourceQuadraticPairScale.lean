module

public import ArtinMatthews.SourceQuadraticPairConductor


set_option backward.privateInPublic true
@[expose] public section

/-! Exact conductor scales after stripping the common exterior ideal. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceQuadraticPairConductor_norm_scaled (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) :
    (q g : ℝ) ^ 2 *
        (sourceQuadraticConductor F S₀ hζ ((b - g) + (c - g))).absNorm =
      (q b : ℝ) * q c := by
  obtain ⟨hgb, hgc, _⟩ := (sourceQuadratic_inf_eq_iff_quotient_disjoint F S₀ b c g).mp hg
  have hbn : (q g : ℝ) * q (b - g) = q b := by
    exact_mod_cast sourceQuadraticExteriorQuotient_norm F S₀ b g hgb
  have hcn : (q g : ℝ) * q (c - g) = q c := by
    exact_mod_cast sourceQuadraticExteriorQuotient_norm F S₀ c g hgc
  rw [sourceQuadraticPairConductor_norm F S₀ hζ b c g hb hc hg hclass, Nat.cast_mul]
  calc
    _ = ((q g : ℝ) * q (b - g)) * ((q g : ℝ) * q (c - g)) := by ring
    _ = _ := by rw [hbn, hcn]

theorem sourceQuadraticPairConductor_norm_quotient (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) :
    ((sourceQuadraticConductor F S₀ hζ ((b - g) + (c - g))).absNorm : ℝ) =
      (q b : ℝ) * q c / (q g : ℝ) ^ 2 := by
  have hqg : (q g : ℝ) ≠ 0 := (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ g)).ne'
  apply (eq_div_iff (pow_ne_zero 2 hqg)).mpr
  simpa only [mul_comm] using
    sourceQuadraticPairConductor_norm_scaled F S₀ hζ b c g hb hc hg hclass

theorem sourceQuadraticPairConductor_sqrt (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) :
    Real.sqrt (sourceQuadraticConductor F S₀ hζ ((b - g) + (c - g))).absNorm =
      Real.sqrt ((q b : ℝ) * q c) / q g := by
  rw [sourceQuadraticPairConductor_norm_quotient F S₀ hζ b c g hb hc hg hclass,
    Real.sqrt_div (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
    Real.sqrt_sq (Nat.cast_nonneg _)]

theorem sourceQuadraticPairConductor_poisson_scale (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (X : ℝ) :
    X / Real.sqrt (sourceQuadraticConductor F S₀ hζ ((b - g) + (c - g))).absNorm =
      X * q g / Real.sqrt ((q b : ℝ) * q c) := by
  rw [sourceQuadraticPairConductor_sqrt F S₀ hζ b c g hb hc hg hclass,
    div_div_eq_mul_div]

theorem sourceQuadraticPairConductor_sqrt_le (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    {N : ℝ} (hbN : (q b : ℝ) ≤ N) (hcN : (q c : ℝ) ≤ N) :
    Real.sqrt (sourceQuadraticConductor F S₀ hζ ((b - g) + (c - g))).absNorm ≤ N / q g := by
  have hN : 0 ≤ N := (Nat.cast_nonneg (q b)).trans hbN
  have hprod : (q b : ℝ) * q c ≤ N ^ 2 := by
    simpa only [pow_two] using mul_le_mul hbN hcN (Nat.cast_nonneg _) hN
  have hsqrt : Real.sqrt ((q b : ℝ) * q c) ≤ N := by
    simpa only [Real.sqrt_sq hN] using Real.sqrt_le_sqrt hprod
  rw [sourceQuadraticPairConductor_sqrt F S₀ hζ b c g hb hc hg hclass]
  exact div_le_div_of_nonneg_right hsqrt (Nat.cast_nonneg _)

theorem sourceQuadraticPairConductor_sqrt_diagonal (b c g : E) (hg : b ⊓ c = g)
    (hbc : b = c) :
    Real.sqrt (sourceQuadraticConductor F S₀ hζ ((b - g) + (c - g))).absNorm = 1 := by
  rw [sourceQuadraticPairConductor_diagonal F S₀ hζ b c g hg hbc, map_one,
    Nat.cast_one, Real.sqrt_one]

end
end ArtinMatthews.SourceEulerAssembly
