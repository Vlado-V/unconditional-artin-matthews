module

public import ArtinMatthews.SourceReflectionExteriorPointwise
public import ArtinMatthews.SourceReflectionSignedExteriorProduct
public import ArtinMatthews.SourceReflectionSupportedFrequency


set_option backward.privateInPublic true
@[expose] public section

/-! The literal signed exterior product has just the actual quadratic
symbol as its common row-column phase. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
  {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
  (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "S" => sourceHilbertSet K S₀
local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "U" => exteriorUnitSubgroup S
local notation "Γ" => SourceExteriorUnitSixthPowers S
local notation "f₀" => sourceReflectionActiveExponents K S₀
local notation "a₀" => sourcePrimeExponentUnit K hζ S₀
local notation "ν" => sourceReflectionExteriorFrequency K S₀ hζ
local notation "D" => sourceReflectionDirectedCofactor K S₀ hζ
local notation "Lext" => sourceReflectionSignedExteriorLocal K S₀ hζ hS
local notation "Πext" => sourceReflectionSignedExteriorProduct K S₀ hζ hS
local notation "Sep" => sourceReflectionExteriorSeparated K S₀ hζ hS

theorem sourceReflectionExteriorFrequency_order (ε : U) (γ : Γ) (f : Finset Pr)
    (a n d c : E) (P : Pr) :
    exteriorPrincipalValuation P.val (ν ε γ f a n d c) =
      ((a + c + 3 • n) P : ℤ) - 2 * ((f₀ f + d) P : ℤ) := by
  rw [sourceReflectionExteriorFrequency, exteriorPrincipalValuation_div,
    exteriorPrincipalValuation_mul, exteriorPrincipalValuation_mul, exteriorPrincipalValuation_pow,
    γ.val.property P.val P.property, ε.property P.val P.property,
    sourceReflectionPrimeExponentUnit_order K S₀ hζ,
    sourceReflectionPrimeExponentUnit_order K S₀ hζ]
  simp only [add_zero, zero_add]
  ring

private theorem prod_extend {α : Type} [DecidableEq α] {s t : Finset α}
    (hst : s ⊆ t) (g : α → ℂ) :
    (∏ p ∈ t, if p ∈ s then g p else 1) = ∏ p ∈ s, g p := by
  rw [← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hst]

private theorem directed_products (d c : ReflectionSquarefreeExponents K S₀)
    (hdc : Disjoint d.val.support c.val.support) :
    (∏ P ∈ d.val.support, (D P c.val : ℂ)) *
        (∏ P ∈ c.val.support, (↑(D P d.val ^ (-4 : ℤ)) : ℂ)) =
      sourceReflectionQuadraticSymbol K S₀ hζ d.val c.val := by
  calc
    _ = (↑((∏ P ∈ d.val.support, D P c.val) *
        (∏ P ∈ c.val.support, D P d.val ^ (-4 : ℤ))) : ℂ) := by
      rw [Units.val_mul]
      exact congrArg₂ (· * ·)
        (map_prod (Units.coeHom ℂ) (fun P : Pr => D P c.val) d.val.support).symm
        (map_prod (Units.coeHom ℂ) (fun P : Pr => D P d.val ^ (-4 : ℤ)) c.val.support).symm
    _ = _ := sourceReflectionDirectedCofactor_pairing K S₀ hζ d c hdc

theorem sourceReflectionSignedExteriorProduct_separated (ε : U) (γ : Γ)
    (h : E) (f : Finset Pr) (a n d c : E)
    (hf : f ∈ sourceReflectionActiveChoices K S₀ h) (ha : a.support ⊆ f)
    (hd : SourceReflectionExteriorRowSupport K S₀ h n d)
    (hc : SourceReflectionExteriorColumnSupport K S₀ f c)
    (hfn : Disjoint f n.support) (hdc : Disjoint d.support c.support) :
    Πext (h + d) (f ∪ d.support) (ν ε γ f a n d c) = Sep ε h f a n d c := by
  let T := ((h.support ∪ d.support) ∪ f) ∪ (c.support ∪ n.support)
  have hhT : h.support ⊆ T := fun _ hp =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hp))
  have hdT : d.support ⊆ T := fun _ hp =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hp))
  have hfT : f ⊆ T := fun _ hp => Finset.mem_union_left _ (Finset.mem_union_right _ hp)
  have hcT : c.support ⊆ T := fun _ hp => Finset.mem_union_right _ (Finset.mem_union_left _ hp)
  have hnT : n.support ⊆ T := fun _ hp => Finset.mem_union_right _ (Finset.mem_union_right _ hp)
  have hiT : h.support \ f ⊆ T := Finset.sdiff_subset.trans hhT
  have hrT : (h + d).support ⊆ T := by
    intro P hP
    rw [sourceReflectionExteriorRow_mem K S₀ h d] at hP
    exact Finset.union_subset hhT hdT hP
  have hactT : f ∪ d.support ⊆ T := Finset.union_subset hfT hdT
  have horder (P : Pr) (hP : P ∉ T) : exteriorPrincipalValuation P.val (ν ε γ f a n d c) = 0 := by
    have hp0 : P ∉ f := fun hp => hP (hfT hp)
    have ha0 := Finsupp.notMem_support_iff.mp (fun hp => hp0 (ha hp))
    have hc0 := Finsupp.notMem_support_iff.mp (fun hp => hP (hcT hp))
    have hn0 := Finsupp.notMem_support_iff.mp (fun hp => hP (hnT hp))
    have hd0 := Finsupp.notMem_support_iff.mp (fun hp => hP (hdT hp))
    rw [sourceReflectionExteriorFrequency_order K S₀ hζ ε γ f a n d c P]
    simp [Finsupp.add_apply, Finsupp.smul_apply, ha0, hc0, hn0, hd0,
      sourceReflectionActiveExponents_apply K S₀, hp0]
  let d' : ReflectionSquarefreeExponents K S₀ := ⟨d,hd.1⟩
  let c' : ReflectionSquarefreeExponents K S₀ := ⟨c,hc.1⟩
  have hdh : Disjoint d.support h.support := (Finset.disjoint_union_right.mp hd.2).1
  have hdn : Disjoint d.support n.support := (Finset.disjoint_union_right.mp hd.2).2
  have hloc (P : Pr) : Lext P (h + d) (f ∪ d.support) (ν ε γ f a n d c) =
      sourceReflectionExteriorPlacedFactors K S₀ hζ hS ε h f a n d c P :=
    sourceReflectionSignedExteriorLocal_factorized K S₀ hζ hS ε γ h f a n d' c'
      hf ha hdh hdn hdc hc.2.symm hfn P
  have hbase :
      (∏ P ∈ T, sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS (a₀ (c + 3 • n))) =
        reflectionGammaTwo K hζ S₀ c /
          ((Real.sqrt (sourcePrimeExponentNorm K S₀ c : ℝ) : ℂ) *
            (sourcePrimeExponentNorm K S₀ n : ℂ)) :=
    sourceKPTameExteriorWhittakerProduct_squarefree_cube K hζ S₀ hS c' n T hcT hnT
  have hpair := directed_products K S₀ hζ d' c' hdc
  change (∏ P ∈ d.support, (D P c : ℂ)) *
      (∏ P ∈ c.support, (↑(D P d ^ (-4 : ℤ)) : ℂ)) =
        sourceReflectionQuadraticSymbol K S₀ hζ d c at hpair
  rw [sourceReflectionSignedExteriorProduct_eq_prod K S₀ hζ hS _ _ _ T hrT hactT horder]
  simp_rw [hloc, sourceReflectionExteriorPlacedFactors]
  simp only [Finset.prod_mul_distrib, prod_extend hiT, prod_extend hfT,
    prod_extend hdT, prod_extend hcT, hbase]
  rw [sourceReflectionExteriorSeparated, sourceReflectionExteriorFrozen, sourceReflectionExteriorRow,
    sourceReflectionExteriorColumn, ite_eq_left hd, ite_eq_left hc, ← hpair]
  simp only [div_eq_mul_inv]
  ac_rfl

theorem sourceReflectionSignedExteriorProduct_supported_index (ε : U) (γ : Γ)
    (h d : E) (f : Finset Pr)
    (hf : f ∈ sourceReflectionActiveChoices K S₀ h) (hd : sourceReflectionIsSquarefree d)
    (hdh : Disjoint d.support h.support)
    (i : SourceReflectionSupportedTermIndex K S₀ f d) :
    Πext (h + d) (f ∪ d.support) (ν ε γ f i.val.1.val i.val.2.1 d i.val.2.2.val) =
      Sep ε h f i.val.1.val i.val.2.1 d i.val.2.2.val := by
  obtain ⟨hr,hc,hdc,hfn⟩ := sourceReflectionExteriorSupport_of_index K S₀ hd hdh i
  exact sourceReflectionSignedExteriorProduct_separated K S₀ hζ hS ε γ h f
    i.val.1.val i.val.2.1 d i.val.2.2.val hf i.val.1.property hr hc hfn hdc

theorem sourceReflectionSignedExteriorProduct_supported_frequency
    (h d : E) (f : Finset Pr)
    (hf : f ∈ sourceReflectionActiveChoices K S₀ h) (hd : sourceReflectionIsSquarefree d)
    (hdh : Disjoint d.support h.support)
    (i : SourceReflectionSupportedTermIndex K S₀ f d)
    (u : ExteriorUnitSixthClasses S) (γ : sNormOneSixthSubgroup K S) :
    Πext (h + d) (f ∪ d.support)
        (sourceReflectionSupportedFrequencyEquiv K S₀ hζ (a₀ (f₀ f + d)) f d (i,u,γ)).val.val =
      Sep (sourceExteriorUnitSixthRepresentative S u) h f i.val.1.val i.val.2.1 d i.val.2.2.val := by
  let γ₀ := (sourceExteriorSixthNormOneEquiv K S).symm γ
  let b := a₀ (f₀ f + d)
  let m := (sourceReflectionCombineNumerator K S₀ f d i).val
  change Πext (h + d) (f ∪ d.support) (sourceReflectionFieldFrequencyEquiv K S₀ hζ b (m,u,γ₀)).val = _
  rw [sourceReflectionFieldFrequencyEquiv_val K S₀ hζ b m u γ₀]
  exact sourceReflectionSignedExteriorProduct_supported_index K S₀ hζ hS
    (sourceExteriorUnitSixthRepresentative S u) γ₀ h d f hf hd hdh i

/-- The original support can be imposed before or after separation. -/
theorem sourceReflectionSignedExteriorProduct_support_extension (ε : U) (γ : Γ)
    (h : E) (f : Finset Pr) (a n d c : E)
    (hf : f ∈ sourceReflectionActiveChoices K S₀ h) (ha : a.support ⊆ f)
    (hfn : Disjoint f n.support) :
    (if SourceReflectionExteriorRowSupport K S₀ h n d ∧
        SourceReflectionExteriorColumnSupport K S₀ f c ∧ Disjoint d.support c.support then
      Πext (h + d) (f ∪ d.support) (ν ε γ f a n d c) else 0) = Sep ε h f a n d c := by
  by_cases hd : SourceReflectionExteriorRowSupport K S₀ h n d
  · by_cases hc : SourceReflectionExteriorColumnSupport K S₀ f c
    · by_cases hdc : Disjoint d.support c.support
      · rw [ite_eq_left ⟨hd,hc,hdc⟩]
        exact sourceReflectionSignedExteriorProduct_separated K S₀ hζ hS ε γ h f
          a n d c hf ha hd hc hfn hdc
      · rw [ite_eq_right (fun h => hdc h.2.2),
          sourceReflectionExteriorSeparated_zero_of_overlap K S₀ hζ hS ε h f a n d c hdc]
    · rw [ite_eq_right (fun h => hc h.2.1), sourceReflectionExteriorSeparated,
        sourceReflectionExteriorColumn_eq_zero_of_not_support K S₀ hζ ε h f a c hc,
        mul_zero, zero_mul, zero_div]
  · rw [ite_eq_right (fun h => hd h.1), sourceReflectionExteriorSeparated,
      sourceReflectionExteriorRow_eq_zero_of_not_support K S₀ hζ hS ε h f a n d hd,
      mul_zero, zero_mul, zero_mul, zero_div]

end
end ArtinMatthews.SourceEulerAssembly
