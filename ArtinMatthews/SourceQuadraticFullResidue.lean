module

public import ArtinMatthews.SourceQuadraticDualFiniteErrors
public import ArtinMatthews.SourceQuadraticSmallResidue


set_option backward.privateInPublic true
@[expose] public section

/-! The literal Full dual residue at a constant squarefree cutoff.
Every divisor coefficient is retained while the positive norm scales cancel. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField Set VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators
noncomputable section

theorem sourceQuadraticFullResidue_scale {X Q N : ℝ}
    (hX : 0 < X) (hQ : 0 < Q) (hN : 0 < N) :
    (X / Real.sqrt Q) * Real.sqrt (Q / (X * N)) =
      Real.sqrt X / Real.sqrt N := by
  rw [Real.sqrt_div hQ.le, Real.sqrt_mul hX.le]
  have hq : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  have hx : Real.sqrt X ≠ 0 := (Real.sqrt_pos.mpr hX).ne'
  have hn : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  calc
    X / Real.sqrt Q * (Real.sqrt Q / (Real.sqrt X * Real.sqrt N)) =
        (X / Real.sqrt X) / Real.sqrt N := by field_simp
    _ = Real.sqrt X / Real.sqrt N := by rw [Real.div_sqrt]

variable (F : Type) [Field F] [NumberField F]

theorem sourceQuadraticSmallResidueFactor_div_norm {M : ℝ} (hM : 0 ≤ M)
    (d : Ideal (𝓞 F)) :
    sourceQuadraticSmallResidueFactor F (M / (Ideal.absNorm d : ℝ)) =
      sourceQuadraticSmallResidueFactor F M / (Real.sqrt (Ideal.absNorm d : ℝ) : ℂ) := by
  unfold sourceQuadraticSmallResidueFactor
  rw [Real.sqrt_div hM]
  push_cast
  ring

variable [IsTotallyComplex F]
variable (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "C" e:max => sourceQuadraticConductor F S₀ hζ e
local notation "Q" e:max => (Ideal.absNorm (C e) : ℝ)

/-- At each divisor scale the conductor factors cancel exactly from the residue. -/
theorem sourceQuadraticDualSquarefreeResidue_scaled (e : E) {X : ℝ}
    (hX : 0 < X) (K : ℝ) :
    ((X / Real.sqrt (Q e) : ℝ) : ℂ) *
        sourceQuadraticDualSquarefreeResidue F S₀ hζ e X K =
      sourceQuadraticSmallResidueFactor F X * quadraticHeckeCoprimeDensity F (C e) *
        ∑ a ∈ quadraticHeckeSquarefreeCutoff F K, quadraticHeckeHalfCoefficient F (Ψ e) a := by
  unfold sourceQuadraticDualSquarefreeResidue
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hna : 0 < (Ideal.absNorm a : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr
        ((mem_quadraticHeckeSquarefreeCutoff F).mp ha).1.ne_zero)
  have hs : ((X / Real.sqrt (Q e) : ℝ) : ℂ) *
        (Real.sqrt (Q e / (X * (Ideal.absNorm a : ℝ))) : ℂ) =
      (Real.sqrt X : ℂ) / (Real.sqrt (Ideal.absNorm a : ℝ) : ℂ) := by
    exact_mod_cast sourceQuadraticFullResidue_scale hX
      (sourceQuadraticDual_conductorNorm_pos F S₀ hζ e) hna
  calc
    _ = (Ψ e).allCoefficient a * (dedekindZeta_residue F : ℂ) *
        ((1 / 2 : ℂ) * mellin sourceQuadraticBlockProfile (1 / 2)) *
        quadraticHeckeCoprimeDensity F (C e) *
        (((X / Real.sqrt (Q e) : ℝ) : ℂ) *
          (Real.sqrt (Q e / (X * (Ideal.absNorm a : ℝ))) : ℂ)) := by ring
    _ = _ := by
      rw [hs, quadraticHeckeHalfCoefficient_eq_div_sqrt]
      unfold sourceQuadraticSmallResidueFactor sourceQuadraticBlockProfile
      ring

/-- The Full residue has the complete fixed-and-common divisor Euler factor. -/
theorem sourceQuadraticDualDivisorResidue_eq_halfCoefficient {M : ℝ} (hM : 0 < M)
    (K : ℝ) (g e : E) :
    sourceQuadraticDualDivisorResidue F S₀ hζ M K g e =
      sourceQuadraticSmallResidueFactor F M * quadraticHeckeCoprimeDensity F (C e) *
        (∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
          (moebius d : ℂ) * quadraticHeckeHalfCoefficient F (Ψ e) d) *
        (∑ a ∈ quadraticHeckeSquarefreeCutoff F K, quadraticHeckeHalfCoefficient F (Ψ e) a) := by
  unfold sourceQuadraticDualDivisorResidue
  conv_rhs => rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hX : 0 < M / (Ideal.absNorm d : ℝ) :=
    div_pos hM (sourceQuadraticBlock_divisorNorm_pos F S₀ g d hd)
  calc
    _ = ((moebius d : ℂ) * (Ψ e).allCoefficient d) *
        (((M / (Ideal.absNorm d : ℝ)) / Real.sqrt (Q e) : ℝ) *
          sourceQuadraticDualSquarefreeResidue F S₀ hζ e (M / (Ideal.absNorm d : ℝ)) K) := by
      push_cast
      ring
    _ = _ := by
      rw [sourceQuadraticDualSquarefreeResidue_scaled F S₀ hζ e hX K,
        sourceQuadraticSmallResidueFactor_div_norm F hM.le,
        quadraticHeckeHalfCoefficient_eq_div_sqrt]
      ring

/-- The actual nonzero Full block with its finite residue in half-coefficient form. -/
theorem sourceQuadraticBlockIdealFull_eq_normalizedResidue {M σ : ℝ}
    (hM : 0 < M) (hσ : 0 < σ) (hσ₁ : σ < 1) (K : ℝ) (g e : E)
    (he : sourceReflectionIsSquarefree e) (hne : e ≠ 0) :
    sourceQuadraticBlockIdealFull F S₀ hζ M g e =
      sourceQuadraticDualDivisorError F S₀ hζ M K σ g e +
        sourceQuadraticSmallResidueFactor F M * quadraticHeckeCoprimeDensity F (C e) *
          (∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
            (moebius d : ℂ) * quadraticHeckeHalfCoefficient F (Ψ e) d) *
          (∑ a ∈ quadraticHeckeSquarefreeCutoff F K, quadraticHeckeHalfCoefficient F (Ψ e) a) +
        sourceQuadraticDualDivisorTail F S₀ hζ M K g e := by
  rw [sourceQuadraticBlockIdealFull_eq_error_residue_tail F S₀ hζ hM hσ hσ₁ K g e he hne,
    sourceQuadraticDualDivisorResidue_eq_halfCoefficient F S₀ hζ hM K g e]

end
end ArtinMatthews.SourceEulerAssembly
