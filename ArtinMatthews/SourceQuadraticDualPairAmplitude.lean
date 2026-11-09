module

public import ArtinMatthews.SourceQuadraticSmallAmplitude
public import ArtinMatthews.SourceQuadraticDualScale
public import ArtinMatthews.SourceQuadraticDualRowInterval


set_option backward.privateInPublic true
@[expose] public section

/-! Literal conductor normalization and the two column phases of a
finite dual row sum. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "C" e:max => sourceQuadraticConductor F S₀ hζ e
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

def sourceQuadraticDualPairAmplitude (rows cols : Finset E)
    (u : E → ℂ) (g d : E) (X : ℝ) (s : ℂ) : ℂ :=
  ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
    star (u p.1) * u p.2 *
      ∑ a ∈ rows, (Ψ ((p.1 - g) + (p.2 - g))).allCoefficient (I a) *
        χ d ((p.1 - g) + (p.2 - g)) *
        ((X / Real.sqrt (Ideal.absNorm (C ((p.1 - g) + (p.2 - g))) : ℝ)) : ℂ) *
        (Real.sqrt ((Ideal.absNorm (C ((p.1 - g) + (p.2 - g))) : ℝ) /
          (X * (q a : ℝ))) : ℂ) ^ s *
        quadraticSmallEuler F (C ((p.1 - g) + (p.2 - g))) s

def sourceQuadraticDualColumnPhase (u : E → ℂ) (g d : E) (R : ℝ) (s : ℂ) (b : E) : ℂ :=
  u (g + b) * χ d b * quadraticPoissonAnnularTwist R (q b) ((s - 1) / 2)

omit [IsTotallyComplex F] in
theorem sourceQuadraticDualPair_conductorEuler (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (s : ℂ) :
    quadraticSmallEuler F (C ((b - g) + (c - g))) s =
      quadraticSmallEuler F (I (b - g)) s * quadraticSmallEuler F (I (c - g)) s := by
  have hdata := sourceQuadraticPair_residual_data F S₀ b c g hb hc hg
  rw [sourceQuadraticPairConductor_eq_product F S₀ hζ b c g hb hc hg hclass]
  exact quadraticSmallEuler_mul F (sourcePrimeExponentIdeal_ne_bot F S₀ _)
    (sourcePrimeExponentIdeal_ne_bot F S₀ _)
    ((sourceQuadraticBlock_ideal_coprime_iff F S₀ _ _).mpr hdata.2.2.1) s

theorem sourceQuadraticDualPairAmplitude_separate (rows cols : Finset E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b)
    (hclass : ∀ b ∈ cols, ∀ c ∈ cols,
      sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (u : E → ℂ) (g d : E) {X R : ℝ} (hX : 0 < X) (hR : 0 < R) (s : ℂ) :
    sourceQuadraticDualPairAmplitude F S₀ hζ rows cols u g d X s =
      (X : ℂ) ^ (1 - s / 2) * (R : ℂ) ^ (s - 1) *
        sourceQuadraticDualEulerRowSum F S₀ hζ rows
          (sourceQuadraticSmallResidualColumns F S₀ cols g)
          (sourceQuadraticDualColumnPhase F S₀ hζ u g d R (star s))
          (sourceQuadraticDualColumnPhase F S₀ hζ u g d R s) s := by
  let pairs := (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g)
  let T (a b c : E) : ℂ := star (u b) * u c * χ a (b - g) * χ a (c - g) *
    χ d (b - g) * χ d (c - g) *
    quadraticPoissonAnnularTwist R (q (b - g)) ((s - 1) / 2) *
    quadraticPoissonAnnularTwist R (q (c - g)) ((s - 1) / 2) *
    quadraticSmallEuler F (I (b - g)) s * quadraticSmallEuler F (I (c - g)) s
  have hp (p : E × E) (hp : p ∈ pairs) :
      star (u p.1) * u p.2 *
        (∑ a ∈ rows, (Ψ ((p.1-g)+(p.2-g))).allCoefficient (I a) *
          χ d ((p.1-g)+(p.2-g)) *
          ((X / Real.sqrt (Ideal.absNorm (C ((p.1-g)+(p.2-g))) : ℝ)) : ℂ) *
          (Real.sqrt ((Ideal.absNorm (C ((p.1-g)+(p.2-g))) : ℝ) /
            (X*(q a : ℝ))) : ℂ)^s * quadraticSmallEuler F (C ((p.1-g)+(p.2-g))) s) =
        (X : ℂ)^(1-s/2) * (R : ℂ)^(s-1) *
          ∑ a ∈ rows, (q a : ℂ)^(-(s/2)) * T a p.1 p.2 := by
    obtain ⟨hmem, hg⟩ := Finset.mem_filter.mp hp
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hmem
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [sourceQuadraticSmallPair_coefficient F S₀ hζ _ _ _ (hcols _ hb) (hcols _ hc) hg,
      sourceQuadraticSymbol_add_right,
      sourceQuadraticDualPair_conductorEuler F S₀ hζ _ _ _ (hcols _ hb) (hcols _ hc)
        hg (hclass _ hb _ hc),
      sourceQuadraticPairConductor_norm F S₀ hζ _ _ _ (hcols _ hb) (hcols _ hc)
        hg (hclass _ hb _ hc), Nat.cast_mul]
    have hscale := quadraticDual_normalized_pair_cpow hX
      (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ (p.1-g)))
      (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ (p.2-g)))
      (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ a)) hR s
    dsimp only [T]
    push_cast at hscale ⊢
    linear_combination (star (u p.1) * u p.2 * χ a (p.1-g) * χ a (p.2-g) *
      χ d (p.1-g) * χ d (p.2-g) * quadraticSmallEuler F (I (p.1-g)) s *
      quadraticSmallEuler F (I (p.2-g)) s) * hscale
  have hpair (a : E) : (∑ p ∈ pairs, T a p.1 p.2) =
      sourceQuadraticSmallCoprimePair F S₀ hζ
        (sourceQuadraticSmallResidualColumns F S₀ cols g) a
        (fun b => sourceQuadraticDualColumnPhase F S₀ hζ u g d R (star s) b *
          star (quadraticSmallEuler F (I b) s))
        (sourceQuadraticSmallEulerCoeff F S₀
          (sourceQuadraticDualColumnPhase F S₀ hζ u g d R s) s) := by
    change (∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g), T a p.1 p.2) = _
    rw [sourceQuadraticSmall_common_pair_reindex F S₀ cols g (T a)]
    unfold sourceQuadraticSmallCoprimePair
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c _
    by_cases hd : Disjoint b.support c.support
    · have hbsf := sourceQuadraticSmallResidualColumns_squarefree F S₀ cols g hcols b hb
      simp only [ite_eq_left hd, T, add_tsub_cancel_left, sourceQuadraticSmallEulerCoeff,
        sourceQuadraticDualColumnPhase, star_mul, star_star]
      rw [sourceQuadraticBlock_symbol_star F S₀ hζ d b hbsf]
      have hstar : (star s - 1) / 2 = star ((s - 1) / 2) := by simp
      rw [hstar, quadraticPoissonAnnularTwist_star hR
        (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ b))]
      ring
    · simp only [ite_eq_right hd]
  change (∑ p ∈ pairs, _) = _
  rw [Finset.sum_congr rfl hp, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  unfold sourceQuadraticDualEulerRowSum
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum, hpair]

end
end ArtinMatthews.SourceEulerAssembly
