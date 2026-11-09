module

public import ArtinMatthews.QuadraticHeckeAnnularComparison
public import ArtinMatthews.SourceQuadraticSieveEnergy
public import ArtinMatthews.SourceQuadraticHeckeSymbols
public import ArtinMatthews.SourceReflectionFrozenWeights


set_option backward.privateInPublic true
@[expose] public section

/-! The tag comparison uses finite prime supports. This file identifies
that representation with the actual squarefree exponent matrix, keeping
the oriented character and both literal norm cuts. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic QuadraticScale
open scoped BigOperators Classical NumberField

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "P" => SourceExteriorPrime F S₀
local notation "E" => ReflectionSquarefreeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "w" => sourceReflectionPrimeNorm F S₀
local notation "active" => sourceReflectionActiveExponents F S₀

theorem sourceQuadraticActive_of_squarefree {e : SourcePrimeExponents F S₀}
    (he : ∀ p, e p ≤ 1) : active e.support = e := by
  ext p
  simp only [sourceReflectionActiveExponents, Finsupp.onFinset_apply]
  by_cases h : p ∈ e.support
  · rw [ite_eq_left h]
    have hn := Finsupp.mem_support_iff.mp h
    have hle := he p
    omega
  · rw [ite_eq_right h, Finsupp.notMem_support_iff.mp h]

theorem sourceQuadraticActive_union (r t : Finset P) (h : Disjoint r t) :
    active (r ∪ t) = active r + active t := by
  ext p
  simp only [sourceReflectionActiveExponents, Finsupp.onFinset_apply, Finsupp.add_apply,
    Finset.mem_union]
  by_cases hr : p ∈ r
  · have ht : p ∉ t := fun h' => Finset.disjoint_left.mp h hr h'
    simp [hr, ht]
  · simp [hr]

def sourceQuadraticSupportEquiv : Finset P ≃ E where
  toFun r := ⟨active r, sourceReflectionActiveExponents_squarefree F S₀ r⟩
  invFun e := e.val.support
  left_inv := sourceReflectionActiveExponents_support F S₀
  right_inv e := Subtype.ext (sourceQuadraticActive_of_squarefree F S₀ e.property)

theorem sourceQuadraticActive_norm (r : Finset P) :
    (q (active r) : ℝ) = supportNorm w r := by
  unfold sourcePrimeExponentNorm Finsupp.prod supportNorm
  rw [sourceReflectionActiveExponents_support]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  simp [sourceReflectionActiveExponents, hp, sourceReflectionPrimeNorm]

def sourceQuadraticSupportKernel (r c : Finset P) : ℂ :=
  reflectionExponentResidueValue F hζ S₀ (active c) (sourcePrimeExponentGenerator F hζ S₀ (active r)) ^ 3

theorem sourceQuadraticSupportKernel_norm_le (r c : Finset P) :
    ‖sourceQuadraticSupportKernel F S₀ hζ r c‖ ≤ 1 := by
  rw [sourceQuadraticSupportKernel, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (reflectionExponentResidueValue_norm_le_one F hζ S₀ _ _)

theorem sourceQuadraticSupportKernel_norm_eq (r c : Finset P) (h : Disjoint r c) :
    ‖sourceQuadraticSupportKernel F S₀ hζ r c‖ = 1 := by
  apply sourceReflectionQuadraticSymbol_norm_eq_one
  simpa only [sourceReflectionActiveExponents_support] using h.symm

theorem sourceQuadraticSupportKernel_union (r t c : Finset P) (h : Disjoint r t) :
    sourceQuadraticSupportKernel F S₀ hζ (r ∪ t) c =
      sourceQuadraticSupportKernel F S₀ hζ r c * sourceQuadraticSupportKernel F S₀ hζ t c := by
  simp only [sourceQuadraticSupportKernel, sourceQuadraticActive_union F S₀ r t h]
  rw [sourceReflectionQuadraticSymbol_reciprocity F S₀ hζ (active c) (active r + active t),
    sourceReflectionQuadraticSymbol_add_left F S₀ hζ (active r) (active t) (active c),
    sourceReflectionQuadraticSymbol_reciprocity F S₀ hζ (active r) (active c),
    sourceReflectionQuadraticSymbol_reciprocity F S₀ hζ (active t) (active c)]

private theorem sourceQuadraticEnergy_map (rows cols : Finset (Finset P)) (a : E → ℂ) :
    sourceQuadraticSieveRowEnergy F S₀ hζ
      (rows.map (sourceQuadraticSupportEquiv F S₀).toEmbedding)
      (cols.map (sourceQuadraticSupportEquiv F S₀).toEmbedding) a =
    finiteEnergy rows cols (sourceQuadraticSupportKernel F S₀ hζ)
      (a ∘ sourceQuadraticSupportEquiv F S₀) := by
  simp only [sourceQuadraticSieveRowEnergy, finiteEnergy, rowValue, Finset.sum_map,
    Equiv.toEmbedding_apply, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  apply mul_comm

private theorem sourceQuadratic_mass_map (cols : Finset (Finset P)) (a : E → ℂ) :
    (∑ e ∈ cols.map (sourceQuadraticSupportEquiv F S₀).toEmbedding, ‖a e‖ ^ 2) =
      coeffMass cols (a ∘ sourceQuadraticSupportEquiv F S₀) := by
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, coeffMass, Function.comp_apply]

theorem sourceQuadraticAdmissible_iff_support (M N B : ℝ) :
    SourceQuadraticDyadicAdmissible F S₀ hζ M N B ↔
      0 ≤ B ∧ AnnularEnergyBound (supportNorm w) (supportNorm w)
        (sourceQuadraticSupportKernel F S₀ hζ) M N B := by
  let e := sourceQuadraticSupportEquiv F S₀
  have henorm (r : Finset P) : (q (e r).val : ℝ) = supportNorm w r :=
    sourceQuadraticActive_norm F S₀ r
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro rows cols hr hc a
    let a' : E → ℂ := a ∘ e.symm
    have H := h.2 (rows.map e.toEmbedding) (cols.map e.toEmbedding) (by
      intro r hr'
      obtain ⟨r', hsmall, rfl⟩ := Finset.mem_map.mp hr'
      rw [Equiv.toEmbedding_apply, henorm]
      exact hr r' hsmall) (by
      intro c hc'
      obtain ⟨c', hsmall, rfl⟩ := Finset.mem_map.mp hc'
      rw [Equiv.toEmbedding_apply, henorm]
      exact hc c' hsmall) a'
    rw [sourceQuadraticEnergy_map, sourceQuadratic_mass_map] at H
    have heq : a' ∘ sourceQuadraticSupportEquiv F S₀ = a :=
      funext fun r => congrArg a (e.symm_apply_apply r)
    rwa [heq] at H
  · rintro ⟨hB, h⟩
    refine ⟨hB, ?_⟩
    intro rows cols hr hc a
    let R := rows.map e.symm.toEmbedding
    let C := cols.map e.symm.toEmbedding
    have hinv (x : E) : supportNorm w (e.symm x) = (q x.val : ℝ) := by
      rw [← henorm, Equiv.apply_symm_apply]
    have H := h R C (by
      intro r hr'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hr'
      rw [Equiv.toEmbedding_apply, hinv]
      exact hr x hx) (by
      intro c hc'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hc'
      rw [Equiv.toEmbedding_apply, hinv]
      exact hc x hx) (a ∘ e)
    have hmap (s : Finset E) : (s.map e.symm.toEmbedding).map e.toEmbedding = s := by
      rw [Finset.map_map]
      have hid : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl E := by
        ext x
        exact e.apply_symm_apply x
      rw [hid, Finset.map_refl]
    rw [← sourceQuadraticEnergy_map, ← sourceQuadratic_mass_map] at H
    change sourceQuadraticSieveRowEnergy F S₀ hζ (R.map e.toEmbedding) (C.map e.toEmbedding) a ≤
      B * ∑ f ∈ C.map e.toEmbedding, ‖a f‖ ^ 2 at H
    simpa only [R, C, hmap] using H

end
end ArtinMatthews.SourceEulerAssembly
