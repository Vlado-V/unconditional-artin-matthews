module

public import ArtinMatthews.SourceQuadraticBlockSupport
public import ArtinMatthews.SourceQuadraticCoefficients
public import ArtinMatthews.SourceQuadraticSelfDual


set_option backward.privateInPublic true
@[expose] public section

/-! Exact common-ideal extraction for the literal B3 block. The row-prime
zero mask survives, and the residual character is the actual primitive
quadratic Hecke coefficient. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

theorem sourceQuadraticBlock_symbol_star (d e : E) (he : sourceReflectionIsSquarefree e) :
    star (χ d e) = χ d e := by
  rw [← sourceQuadraticRayCharacter_allCoefficient F S₀ hζ e he d]
  exact sourceQuadraticRayCharacter_star_allCoefficient F S₀ hζ e _

omit [IsTotallyComplex F] in
theorem sourceQuadraticBlock_residual_squarefree (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hdis : Disjoint (b-g).support (c-g).support) :
    sourceReflectionIsSquarefree ((b-g)+(c-g)) := by
  have hb' := sourceQuadraticExteriorQuotient_squarefree F S₀ b g hb
  have hc' := sourceQuadraticExteriorQuotient_squarefree F S₀ c g hc
  intro P
  have hz : (b-g) P = 0 ∨ (c-g) P = 0 := by
    by_contra! hn
    exact Finset.disjoint_left.mp hdis (Finsupp.mem_support_iff.mpr hn.1)
      (Finsupp.mem_support_iff.mpr hn.2)
  have hbP := hb' P
  have hcP := hc' P
  simp only [Finsupp.add_apply]
  omega

theorem sourceQuadraticBlock_pair_factor (a : E → ℂ) (d b c g : E)
    (hgb : g ≤ b) (hgc : g ≤ c) (hb : sourceReflectionIsSquarefree b) :
    sourceQuadraticPairValue F S₀ hζ a d (b,c) =
      if Disjoint d.support g.support then
        star (a b)*a c*χ d ((b-g)+(c-g)) else 0 := by
  have hbχ : χ d b = χ d g * χ d (b-g) := by
    rw [← sourceQuadraticSymbol_add_right, add_tsub_cancel_of_le hgb]
  have hcχ : χ d c = χ d g * χ d (c-g) := by
    rw [← sourceQuadraticSymbol_add_right, add_tsub_cancel_of_le hgc]
  have hnorm : ((‖χ d g‖^2 : ℝ) : ℂ) = star (χ d g)*χ d g := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rfl
  have hmask : star (χ d g)*χ d g = if Disjoint d.support g.support then 1 else 0 :=
    hnorm.symm.trans (sourceQuadraticBlock_symbol_mask F S₀ hζ d g)
  unfold sourceQuadraticPairValue
  rw [hbχ, hcχ]
  simp only [star_mul]
  rw [sourceQuadraticBlock_symbol_star F S₀ hζ d (b-g)
    (sourceQuadraticExteriorQuotient_squarefree F S₀ b g hb)]
  calc
    _ = (star (χ d g)*χ d g)*(star (a b)*a c)*(χ d (b-g)*χ d (c-g)) := by ring
    _ = (if Disjoint d.support g.support then 1 else 0)*
        (star (a b)*a c)*χ d ((b-g)+(c-g)) := by
      rw [hmask, ← sourceQuadraticSymbol_add_right]
    _ = _ := by split_ifs <;> simp

/-- Exact finite B3 correspondence, before any analytic estimate. -/
theorem sourceQuadraticB3Block_eq_character_rows (rows cols : Finset E) (w : E → ℝ)
    (a : E → ℂ) (g : E) (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b) :
    sourceQuadraticB3Block F S₀ hζ rows cols w a g =
      ∑ p ∈ (cols ×ˢ cols).filter (fun p : E×E => p.1 ⊓ p.2 = g),
        star (a p.1)*a p.2*
          sourceQuadraticBlockRowKernel F S₀ hζ rows w g ((p.1-g)+(p.2-g)) := by
  unfold sourceQuadraticB3Block
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpair,hg⟩ := Finset.mem_filter.mp hp
  obtain ⟨hb,hc⟩ := Finset.mem_product.mp hpair
  have hgb : g ≤ p.1 := hg ▸ inf_le_left
  have hgc : g ≤ p.2 := hg ▸ inf_le_right
  unfold sourceQuadraticBlockRowKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [sourceQuadraticBlock_pair_factor F S₀ hζ a d p.1 p.2 g hgb hgc (hcols p.1 hb)]
  by_cases hd : Disjoint d.support g.support
  · simp only [ite_eq_left hd]
    ring
  · simp only [ite_eq_right hd, mul_zero]

/-- The same block indexed by its original divisible columns, retaining the
coprime residual-column condition. -/
theorem sourceQuadraticB3Block_eq_divisible_character_rows
    (rows cols : Finset E) (w : E → ℝ) (a : E → ℂ) (g : E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b) :
    sourceQuadraticB3Block F S₀ hζ rows cols w a g =
      ∑ b ∈ sourceQuadraticDivisibleColumns F S₀ cols g,
        ∑ c ∈ sourceQuadraticDivisibleColumns F S₀ cols g,
          if Disjoint (b-g).support (c-g).support then
            star (a b)*a c*sourceQuadraticBlockRowKernel F S₀ hζ rows w g ((b-g)+(c-g)) else 0 := by
  rw [sourceQuadraticB3Block_eq_character_rows F S₀ hζ rows cols w a g hcols,
    sourceQuadratic_common_pairs_eq_divisible, Finset.sum_filter, Finset.sum_product]

end
end ArtinMatthews.SourceEulerAssembly
