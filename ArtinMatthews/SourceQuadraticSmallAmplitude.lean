module

public import ArtinMatthews.SourceQuadraticSmallPairEuler
public import ArtinMatthews.SourceQuadraticSmallRows
public import ArtinMatthews.SourceQuadraticSmallCofactors
public import ArtinMatthews.SourceQuadraticSmallEulerBall


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ

/-- The literal finite pair and squarefree-row amplitude of the Small error. -/
def sourceQuadraticOriginalSmallAmplitude (K : ℝ) (cols : Finset E)
    (u : E → ℂ) (g : E) (s : ℂ) : ℂ :=
  ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
    star (u p.1) * u p.2 *
      ∑ a ∈ sourceQuadraticSmallRows F S₀ K g,
        (Ψ ((p.1 - g) + (p.2 - g))).allCoefficient (I a) * (q a : ℂ) ^ (-(s / 2)) *
          quadraticSmallEuler F (sourceQuadraticBlockSquareModulus F S₀ hζ g
            ((p.1 - g) + (p.2 - g))) s

theorem sourceQuadraticSmallPair_coefficient (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g) (a : E) :
    (Ψ ((b - g) + (c - g))).allCoefficient (I a) = χ a (b - g) * χ a (c - g) := by
  rw [sourceQuadraticRayCharacter_allCoefficient F S₀ hζ _
    (sourceQuadraticPair_residual_data F S₀ b c g hb hc hg).2.2.2,
    sourceQuadraticSymbol_add_right]

theorem sourceQuadraticOriginalSmallAmplitude_separate (K : ℝ) (cols : Finset E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b)
    (hclass : ∀ b ∈ cols, ∀ c ∈ cols,
      sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (u : E → ℂ) (g : E) (s : ℂ) :
    sourceQuadraticOriginalSmallAmplitude F S₀ hζ K cols u g s =
      quadraticSmallEuler F (sourceQuadraticBlockModulus F S₀ g) s *
        sourceQuadraticSmallEulerRowSum F S₀ hζ (sourceQuadraticSmallRows F S₀ K g)
          (sourceQuadraticSmallResidualColumns F S₀ cols g)
          (sourceQuadraticSmallResidualCoeff F S₀ g u) s := by
  let pairs := (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g)
  let rows := sourceQuadraticSmallRows F S₀ K g
  let T (a b c : E) : ℂ := star (u b) * u c * χ a (b - g) * χ a (c - g) *
    quadraticSmallEuler F (I (b - g)) s * quadraticSmallEuler F (I (c - g)) s
  have hp (p : E × E) (hp : p ∈ pairs) :
      star (u p.1) * u p.2 *
        (∑ a ∈ rows, (Ψ ((p.1 - g) + (p.2 - g))).allCoefficient (I a) *
          (q a : ℂ) ^ (-(s / 2)) * quadraticSmallEuler F
            (sourceQuadraticBlockSquareModulus F S₀ hζ g ((p.1 - g) + (p.2 - g))) s) =
        quadraticSmallEuler F (sourceQuadraticBlockModulus F S₀ g) s *
          ∑ a ∈ rows, (q a : ℂ) ^ (-(s / 2)) * T a p.1 p.2 := by
    obtain ⟨hmem, hg⟩ := Finset.mem_filter.mp hp
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hmem
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [sourceQuadraticSmallPair_coefficient F S₀ hζ _ _ _ (hcols _ hb) (hcols _ hc) hg,
      sourceQuadraticSmallPairEuler F S₀ hζ _ _ _ (hcols _ hb) (hcols _ hc) hg (hclass _ hb _ hc)]
    dsimp only [T]
    ring
  have hpair (a : E) :
      (∑ p ∈ pairs, T a p.1 p.2) =
        sourceQuadraticSmallCoprimePair F S₀ hζ
          (sourceQuadraticSmallResidualColumns F S₀ cols g) a
          (fun b => sourceQuadraticSmallResidualCoeff F S₀ g u b *
            star (quadraticSmallEuler F (I b) s))
          (sourceQuadraticSmallEulerCoeff F S₀ (sourceQuadraticSmallResidualCoeff F S₀ g u) s) := by
    change (∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g), T a p.1 p.2) = _
    rw [sourceQuadraticSmall_common_pair_reindex F S₀ cols g (T a)]
    unfold sourceQuadraticSmallCoprimePair
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    by_cases hd : Disjoint b.support c.support
    · simp only [ite_eq_left hd, T, add_tsub_cancel_left, sourceQuadraticSmallEulerCoeff,
        sourceQuadraticSmallResidualCoeff, star_mul, star_star]
      ring
    · simp only [ite_eq_right hd]
  change (∑ p ∈ pairs, _) = _
  rw [Finset.sum_congr rfl hp]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  unfold sourceQuadraticSmallEulerRowSum
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum, hpair]

end
end ArtinMatthews.SourceEulerAssembly
