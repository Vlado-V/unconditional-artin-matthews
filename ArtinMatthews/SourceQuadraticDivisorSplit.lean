module

public import ArtinMatthews.SourceQuadraticShortColumns


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

private theorem disjoint_values (b c : E) (h : Disjoint b.support c.support)
    (P : SourceExteriorPrime F S₀) : b P = 0 ∨ c P = 0 := by
  by_cases hb : b P = 0
  · exact Or.inl hb
  · exact Or.inr (by
      by_contra hc
      exact Finset.disjoint_left.mp h (Finsupp.mem_support_iff.mpr hb) (Finsupp.mem_support_iff.mpr hc))

theorem sourceQuadraticDivisor_split (d b c : E) (hbc : Disjoint b.support c.support)
    (hd : d ≤ b + c) : (d ⊓ b) + (d ⊓ c) = d := by
  ext P
  have hp := hd P
  have hz := disjoint_values F S₀ b c hbc P
  simp only [Finsupp.add_apply, Finsupp.inf_apply] at hp ⊢
  change min (d P) (b P) + min (d P) (c P) = d P
  omega

theorem sourceQuadraticDivisor_fiber_iff (d e b c : E) (he : e ≤ d)
    (hbc : Disjoint b.support c.support) :
    (d ≤ b + c ∧ d ⊓ b = e) ↔ e ≤ b ∧ d - e ≤ c := by
  constructor
  · rintro ⟨hd, rfl⟩
    refine ⟨inf_le_right, fun P => ?_⟩
    have hp := hd P
    have hz := disjoint_values F S₀ b c hbc P
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.inf_apply] at hp ⊢
    change d P - min (d P) (b P) ≤ c P
    omega
  · rintro ⟨hb, hc⟩
    have hsum : d ≤ b + c := by
      intro P
      have hd := he P
      have hb' := hb P
      have hc' := hc P
      simp only [Finsupp.tsub_apply, Finsupp.add_apply] at hc' ⊢
      omega
    refine ⟨hsum, ?_⟩
    ext P
    have hd := he P
    have hb' := hb P
    have hc' := hc P
    have hz := disjoint_values F S₀ b c hbc P
    simp only [Finsupp.tsub_apply, Finsupp.inf_apply] at hc' ⊢
    change min (d P) (b P) = e P
    omega

def sourceQuadraticDivisorPairSum (cols : Finset E) (a d : E) (coeffLeft coeffRight : E → ℂ) : ℂ :=
  ∑ b ∈ cols, ∑ c ∈ cols,
    if Disjoint b.support c.support ∧ d ≤ b + c then
      star (coeffLeft b) * coeffRight c * χ a b * χ a c else 0

def sourceQuadraticSplitPairSum (cols : Finset E) (a d₁ d₂ : E) (coeffLeft coeffRight : E → ℂ) : ℂ :=
  ∑ b ∈ sourceQuadraticDivisibleColumns F S₀ cols d₁,
    ∑ c ∈ sourceQuadraticDivisibleColumns F S₀ cols d₂,
      if Disjoint b.support c.support then star (coeffLeft b) * coeffRight c * χ a b * χ a c else 0

def sourceQuadraticDivisorDyad (D : ℝ) : Finset E :=
  (sourceReflectionBoundedExponents F S₀ (2 * D)).filter (fun d => D ≤ (q d : ℝ))

def sourceQuadraticDivisorBilinearSum (rows cols : Finset E) (D : ℝ) (coeffLeft coeffRight : E → ℂ) : ℝ :=
  ∑ d ∈ sourceQuadraticDivisorDyad F S₀ D, ∑ a ∈ rows,
    ‖sourceQuadraticDivisorPairSum F S₀ hζ cols a d coeffLeft coeffRight‖

theorem sourceQuadraticDivisorPairSum_eq_split (cols : Finset E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b) (a d : E) (coeffLeft coeffRight : E → ℂ) :
    sourceQuadraticDivisorPairSum F S₀ hζ cols a d coeffLeft coeffRight =
      ∑ e ∈ sourceQuadraticSquarefreeDivisors F S₀ d,
        sourceQuadraticSplitPairSum F S₀ hζ cols a e (d - e) coeffLeft coeffRight := by
  let pairs := (cols ×ˢ cols).filter (fun p : E × E => Disjoint p.1.support p.2.support ∧ d ≤ p.1 + p.2)
  let value (p : E × E) := star (coeffLeft p.1) * coeffRight p.2 * χ a p.1 * χ a p.2
  have hm (p : E × E) (hp : p ∈ pairs) :
      d ⊓ p.1 ∈ sourceQuadraticSquarefreeDivisors F S₀ d := by
    obtain ⟨hpcols, _⟩ := Finset.mem_filter.mp hp
    refine (sourceQuadratic_mem_squarefreeDivisors F S₀ d _).mpr ⟨inf_le_left, fun P => ?_⟩
    exact (inf_le_right : d ⊓ p.1 ≤ p.1) P |>.trans (hcols p.1 (Finset.mem_product.mp hpcols).1 P)
  have hf (e : E) (he : e ∈ sourceQuadraticSquarefreeDivisors F S₀ d) :
      pairs.filter (fun p => d ⊓ p.1 = e) =
        ((sourceQuadraticDivisibleColumns F S₀ cols e) ×ˢ
          (sourceQuadraticDivisibleColumns F S₀ cols (d - e))).filter
            (fun p => Disjoint p.1.support p.2.support) := by
    ext p
    have hed := ((sourceQuadratic_mem_squarefreeDivisors F S₀ d e).mp he).1
    simp only [pairs, Finset.mem_filter, Finset.mem_product,
      sourceQuadratic_mem_divisibleColumns]
    by_cases hbc : Disjoint p.1.support p.2.support
    · have hiff := sourceQuadraticDivisor_fiber_iff F S₀ d e p.1 p.2 hed hbc
      tauto
    · simp [hbc]
  calc
    _ = ∑ p ∈ pairs, value p := by
      simp only [pairs, value, Finset.sum_filter, Finset.sum_product, sourceQuadraticDivisorPairSum]
    _ = ∑ e ∈ sourceQuadraticSquarefreeDivisors F S₀ d,
          ∑ p ∈ pairs.filter (fun p => d ⊓ p.1 = e), value p :=
      (Finset.sum_fiberwise_of_maps_to hm value).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hf e he]
      simp only [sourceQuadraticSplitPairSum, Finset.sum_filter, Finset.sum_product, value]

end
end ArtinMatthews.SourceEulerAssembly
