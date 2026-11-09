module

public import ArtinMatthews.SourceKPRetainedExteriorLocalSupport
public import ArtinMatthews.SourceKPExteriorWhittakerProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The exterior spherical Whittaker product is supported on the actual
nonnegative orders in the two admissible congruence classes. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil Filter
open scoped NumberField nonZeroDivisors Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "S[" S₀ "]" => sourceHilbertSet K S₀
local notation "W" => sourceKPTameExteriorWhittakerDiagonal K hζ

private theorem exterior_orders_finite (S₀ : Finset Pr) (m : Kˣ) :
    Set.Finite {P : SourceExteriorPrime K S₀ | exteriorPrincipalValuation P.val m ≠ 0} := by
  have h : Set.Finite {P : Pr | exteriorPrincipalValuation P m ≠ 0} := by
    exact Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors
      (toPrincipalIdeal (𝓞 K) K m : FractionalIdeal (𝓞 K)⁰ K))
  change ((Subtype.val : SourceExteriorPrime K S₀ → Pr) ⁻¹'
    {P : Pr | exteriorPrincipalValuation P m ≠ 0}).Finite
  exact Set.Finite.preimage Subtype.val_injective.injOn h

def sourceKPRetainedExteriorOrderSupport (S₀ : Finset Pr) (m : Kˣ) :
    Finset (SourceExteriorPrime K S₀) :=
  (exterior_orders_finite K S₀ m).toFinset

theorem sourceKPRetainedExteriorOrderSupport_mem (S₀ : Finset Pr) (m : Kˣ)
    (P : SourceExteriorPrime K S₀) :
    P ∈ sourceKPRetainedExteriorOrderSupport K S₀ m ↔ exteriorPrincipalValuation P.val m ≠ 0 :=
  (exterior_orders_finite K S₀ m).mem_toFinset

def sourceKPRetainedExteriorWhittaker
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀]) (m : Kˣ) : ℂ :=
  ∏ᶠ P : SourceExteriorPrime K S₀, W S₀ P hS m

theorem sourceKPRetainedExteriorWhittaker_support_subset
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀]) (m : Kˣ) :
    Function.mulSupport (fun P : SourceExteriorPrime K S₀ => W S₀ P hS m) ⊆
      sourceKPRetainedExteriorOrderSupport K S₀ m := by
  intro P hP
  apply (sourceKPRetainedExteriorOrderSupport_mem K S₀ m P).mpr
  intro he
  exact hP (sourceKPRetainedExteriorLocal_one_of_order_zero K hζ S₀ hS P m he)

theorem sourceKPRetainedExteriorWhittaker_finite_support
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀]) (m : Kˣ) :
    Function.HasFiniteMulSupport (fun P : SourceExteriorPrime K S₀ => W S₀ P hS m) :=
  (sourceKPRetainedExteriorOrderSupport K S₀ m).finite_toSet.subset
    (sourceKPRetainedExteriorWhittaker_support_subset K hζ S₀ hS m)

theorem sourceKPRetainedExteriorWhittaker_eq_prod
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀]) (m : Kˣ) :
    sourceKPRetainedExteriorWhittaker K hζ S₀ hS m =
      ∏ P ∈ sourceKPRetainedExteriorOrderSupport K S₀ m, W S₀ P hS m :=
  finprod_eq_prod_of_mulSupport_subset _ (sourceKPRetainedExteriorWhittaker_support_subset K hζ S₀ hS m)

theorem sourceKPRetainedExteriorWhittaker_zero_of_bad_order
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀]) (m : Kˣ)
    (P : SourceExteriorPrime K S₀)
    (hm : exteriorPrincipalValuation P.val m < 0 ∨ exteriorPrincipalValuation P.val m % 3 = 2) :
    sourceKPRetainedExteriorWhittaker K hζ S₀ hS m = 0 :=
  finprod_eq_zero _ P (sourceKPRetainedExteriorLocal_zero_of_bad_order K hζ S₀ hS P m hm)
    (sourceKPRetainedExteriorWhittaker_finite_support K hζ S₀ hS m)

theorem sourceKPRetainedExteriorWhittaker_nonzero_orders
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀]) (m : Kˣ)
    (hm : sourceKPRetainedExteriorWhittaker K hζ S₀ hS m ≠ 0) (P : SourceExteriorPrime K S₀) :
    0 ≤ exteriorPrincipalValuation P.val m ∧ exteriorPrincipalValuation P.val m % 3 ≠ 2 := by
  have hbad (h : exteriorPrincipalValuation P.val m < 0 ∨
      exteriorPrincipalValuation P.val m % 3 = 2) : False :=
    hm (sourceKPRetainedExteriorWhittaker_zero_of_bad_order K hζ S₀ hS m P h)
  exact ⟨le_of_not_gt (fun h => hbad (Or.inl h)), fun h => hbad (Or.inr h)⟩

theorem sourceKPRetainedExteriorWhittaker_nonzero_sourceRing
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀]) (m : Kˣ)
    (hm : sourceKPRetainedExteriorWhittaker K hζ S₀ hS m ≠ 0) :
    ∃ x : sourceRing K S₀, (x:K) = (m:K) := by
  refine ⟨⟨(m:K),?_⟩,rfl⟩
  intro P hP
  have he := (sourceKPRetainedExteriorWhittaker_nonzero_orders K hζ S₀ hS m hm ⟨P,hP⟩).1
  change 0 ≤ exteriorPrincipalValuation P m at he
  have hv := sourceKPRetainedRationalLocalUnit_valuation K P m
  change Valued.v (((m:K):P.adicCompletion K)) = _ at hv
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
  rw [hv]
  exact WithZero.exp_le_one_iff.mpr (by omega)

theorem sourceKPRetainedExteriorWhittaker_mul_sixth
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀]) (m r : Kˣ)
    (hr : ∀ P ∉ S[S₀], P.valuation K (r:K) = 1) :
    sourceKPRetainedExteriorWhittaker K hζ S₀ hS (m*r^6) =
      sourceKPRetainedExteriorWhittaker K hζ S₀ hS m := by
  unfold sourceKPRetainedExteriorWhittaker
  apply finprod_congr
  intro P
  exact sourceKPRetainedExteriorLocal_mul_sixth K hζ S₀ hS P m r (hr P.val P.property)

theorem sourceKPRetainedExteriorWhittaker_mul_exterior_sixth
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀]) (m : Kˣ)
    (r : exteriorUnitSubgroup S[S₀]) :
    sourceKPRetainedExteriorWhittaker K hζ S₀ hS (m*r.val^6) =
      sourceKPRetainedExteriorWhittaker K hζ S₀ hS m :=
  sourceKPRetainedExteriorWhittaker_mul_sixth K hζ S₀ hS m r.val
    (fun P hP => (sourceExteriorPrincipalValuation_eq_zero_iff K P r.val).mp (r.property P hP))

theorem sourceKPRetainedExteriorWhittaker_squarefree_cube
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀])
    (c : ReflectionSquarefreeExponents K S₀) (n : SourcePrimeExponents K S₀) :
    sourceKPRetainedExteriorWhittaker K hζ S₀ hS (sourcePrimeExponentUnit K hζ S₀ (c.val+3•n)) =
      reflectionGammaTwo K hζ S₀ c.val /
        ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) * (sourcePrimeExponentNorm K S₀ n : ℂ)) := by
  let m := sourcePrimeExponentUnit K hζ S₀ (c.val+3•n)
  let f (P : SourceExteriorPrime K S₀) := W S₀ P hS m
  have he : (∏' P, f P) = ∏ᶠ P, f P :=
    tprod_eq_finprod (sourceKPRetainedExteriorWhittaker_finite_support K hζ S₀ hS m)
  exact he.symm.trans (sourceKPTameExteriorWhittaker_tprod K hζ S₀ hS c n)

theorem sourceKPRetainedExteriorWhittaker_squarefree_cube_mul_sixth
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀])
    (c : ReflectionSquarefreeExponents K S₀) (n : SourcePrimeExponents K S₀) (r : exteriorUnitSubgroup S[S₀]) :
    sourceKPRetainedExteriorWhittaker K hζ S₀ hS (sourcePrimeExponentUnit K hζ S₀ (c.val+3•n)*r.val^6) =
      reflectionGammaTwo K hζ S₀ c.val /
        ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) * (sourcePrimeExponentNorm K S₀ n : ℂ)) := by
  rw [sourceKPRetainedExteriorWhittaker_mul_exterior_sixth, sourceKPRetainedExteriorWhittaker_squarefree_cube]

end
end ArtinMatthews
