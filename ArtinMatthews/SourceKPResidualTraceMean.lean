module

public import ArtinMatthews.SourceKPTranslateTraceAEAlgebra
public import ArtinMatthews.SourceKPAdelicTraceConstantTerm


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite trace and the normalized adelic integral
commute by relabelling the full finite fiber, including its multiplicities. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local instance sourceTraceMeanAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _
local instance sourceTraceMeanAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

variable (F : Finset (SourceKPFiniteAdeleProjective K hζ))
variable (t : SourceKPFiniteAdeleProjective K hζ)
variable (ht : sourceKPFiniteTranslateLevel K hζ F ≤ sourceKPFiniteLevelConjugate K hζ t)
local notation "U" => SourceKPArchUpperHalfSpace K
local notation "B" => SourceKPFiniteLevelFiber K hζ
local notation "BJ" => SourceKPTranslateFiniteLevelFiber K hζ F
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ F
local notation "L[" b "]" => {c : BJ // sourceKPFiniteRightTranslateMap K hζ F t ht c = b}

theorem sourceKPTranslateCompactTrace_moving_upper
    (v : YJ → ℂ) (b : B) (p : U) (g : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPTranslateCompactTrace K hζ F t ht v (sourceKPUpperToCompact K hζ (g • b) p) =
      ∑ c : L[b], v (sourceKPTranslateUpperMk K hζ F (p,g • c.val)) := by
  classical
  rw [sourceKPTranslateCompactTrace_upper]
  let e := sourceKPFiniteRightTranslateFiberSmulEquiv K hζ F t ht g b
  symm
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem sourceKPTranslateCompactTrace_adelic_integral
    (v : YJ → ℂ) (b : B) (p : 𝔸[K] → U)
    (g : 𝔸[K] → SourceKPFiniteAdeleProjective K hζ)
    (hi : ∀ c : L[b], IntegrableOn
      (fun a => v (sourceKPTranslateUpperMk K hζ F (p a,g a • c.val)))
      (sourceKPAdelicFundamentalDomain K) (sourceKPAdelicTraceProduct K)) :
    (∫ a in sourceKPAdelicFundamentalDomain K,
      sourceKPTranslateCompactTrace K hζ F t ht v
        (sourceKPUpperToCompact K hζ (g a • b) (p a)) ∂sourceKPAdelicTraceProduct K) =
      ∑ c : L[b], ∫ a in sourceKPAdelicFundamentalDomain K,
        v (sourceKPTranslateUpperMk K hζ F (p a,g a • c.val)) ∂sourceKPAdelicTraceProduct K := by
  classical
  simp_rw [sourceKPTranslateCompactTrace_moving_upper K hζ F t ht]
  exact integral_finset_sum Finset.univ (fun c _ => hi c)

theorem sourceKPTranslateCompactTrace_adelic_integral_eq_zero
    (v : YJ → ℂ) (b : B) (p : 𝔸[K] → U)
    (g : 𝔸[K] → SourceKPFiniteAdeleProjective K hζ)
    (hi : ∀ c : L[b], IntegrableOn
      (fun a => v (sourceKPTranslateUpperMk K hζ F (p a,g a • c.val)))
      (sourceKPAdelicFundamentalDomain K) (sourceKPAdelicTraceProduct K))
    (hz : ∀ c : L[b], (∫ a in sourceKPAdelicFundamentalDomain K,
      v (sourceKPTranslateUpperMk K hζ F (p a,g a • c.val)) ∂sourceKPAdelicTraceProduct K) = 0) :
    (∫ a in sourceKPAdelicFundamentalDomain K,
      sourceKPTranslateCompactTrace K hζ F t ht v
        (sourceKPUpperToCompact K hζ (g a • b) (p a)) ∂sourceKPAdelicTraceProduct K) = 0 := by
  rw [sourceKPTranslateCompactTrace_adelic_integral K hζ F t ht v b p g hi]
  exact Finset.sum_eq_zero (fun c _ => hz c)

end
end ArtinMatthews
