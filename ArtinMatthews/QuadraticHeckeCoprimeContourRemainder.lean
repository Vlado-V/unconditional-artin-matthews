module

public import ArtinMatthews.QuadraticHeckeCoprimeDensity
public import ArtinMatthews.QuadraticHeckeSquareNormContour


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Complex Set MeasureTheory VaryingKummerAnalytic SourcePhysical
  UniqueFactorizationMonoid
open OAI.SevenEighths.ProbePhysical
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- The finite Möbius sum of the contour integrals at their actual divisor scales. -/
def quadraticHeckeCoprimeContourRemainder (m : Ideal (𝓞 F))
    (H : ℂ → ℂ) (σ X : ℝ) : ℂ :=
  ∑ d ∈ HeckeIdealMobius.divisors F m, (moebius d : ℂ) *
    verticalIntegral σ (fun s : ℂ =>
      (((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) ^ s) * H s * mixedDedekindZeta F s)

theorem quadraticHeckeCoprime_divisor_norm_pos
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) {d : Ideal (𝓞 F)}
    (hd : d ∈ HeckeIdealMobius.divisors F m) : 0 < (Ideal.absNorm d : ℝ) := by
  have hd0 : d ≠ ⊥ := by
    intro hzero
    obtain ⟨J, hJ⟩ := (HeckeIdealMobius.mem_divisors F hm).mp hd
    exact hm (by rw [hJ, hzero, Ideal.bot_mul])
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hd0)

/-- The residue factors out of the finite Möbius sum without changing the contour terms. -/
theorem quadraticHeckeCoprimeContour_residue
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (H : ℂ → ℂ) (σ X : ℝ) (A B : ℂ) :
    (∑ d ∈ HeckeIdealMobius.divisors F m, (moebius d : ℂ) *
      (verticalIntegral σ (fun s : ℂ =>
        (((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) ^ s) * H s * mixedDedekindZeta F s) +
          A * ((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) * B)) =
      quadraticHeckeCoprimeContourRemainder F m H σ X +
        A * (X : ℂ) * B * quadraticHeckeCoprimeDensity F m := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  change quadraticHeckeCoprimeContourRemainder F m H σ X + _ = _
  congr 1
  calc
    _ = ∑ d ∈ HeckeIdealMobius.divisors F m,
        (moebius d : ℂ) * ((A * B) * ((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = (A * B) * (X : ℂ) * quadraticHeckeCoprimeDensity F m :=
      quadraticHeckeCoprimeDensity_rescaled_sum F m hm X (A * B)
    _ = _ := by ring

end
end ArtinMatthews
