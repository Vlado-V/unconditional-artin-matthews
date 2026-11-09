module

public import ArtinMatthews.SourceKPExteriorTensorUniqueness


set_option backward.privateInPublic true
@[expose] public section

/-! Exact upper-root equivariance of the finite exterior tensor.
Each place acts through its actual local cyclic representation. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators TensorProduct
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (SourceExteriorPrime K S₀))
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "V" => SourceKPExteriorTensor K hζ S₀ T
local notation "ρ₀" => sourceKPExteriorTensorRepresentation K hζ S₀ T
local notation "λ₀" => sourceKPExteriorTensorWhittaker K hζ S₀ T hS
local notation "G₀" => SourceKPExteriorProductGroup K hζ S₀ T

def sourceKPExteriorUpperTuple (x : (P : T) → P.val.val.adicCompletion K) : G₀ :=
  fun P => sourceFiniteKP2ProjectiveLift K hζ P.val.val (sourceGL2Upper (x P))

theorem sourceKPExteriorTensorWhittaker_upper
    (x : (P : T) → P.val.val.adicCompletion K) (v : V) :
    λ₀ (ρ₀ (sourceKPExteriorUpperTuple K hζ S₀ T x) v) =
      (∏ P : T, localFiniteCharacter K P.val.val (x P)) * λ₀ v := by
  have he : (λ₀).comp (ρ₀ (sourceKPExteriorUpperTuple K hζ S₀ T x)) =
      (∏ P : T, localFiniteCharacter K P.val.val (x P)) • λ₀ := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    change λ₀ (PiTensorProduct.map _ (PiTensorProduct.tprod ℂ f)) = _
    rw [PiTensorProduct.map_tprod, sourceKPExteriorTensorWhittaker_tprod]
    change (∏ P : T, sourceKPTameCyclicWhittaker K hζ S₀ P.val hS
      (sourceKPTameSphericalCyclicRepresentation K hζ S₀ P.val
        (sourceFiniteKP2ProjectiveLift K hζ P.val.val (sourceGL2Upper (x P))) (f P))) =
      (∏ P : T, localFiniteCharacter K P.val.val (x P)) * λ₀ (PiTensorProduct.tprod ℂ f)
    simp_rw [sourceKPTameCyclicWhittaker_upper]
    rw [Finset.prod_mul_distrib, sourceKPExteriorTensorWhittaker_tprod]
  exact LinearMap.congr_fun he v

theorem sourceKPExteriorTensorWhittaker_single_upper (P : T) (x : P.val.val.adicCompletion K) (v : V) :
    λ₀ (ρ₀ (Pi.mulSingle P (sourceFiniteKP2ProjectiveLift K hζ P.val.val (sourceGL2Upper x))) v) =
      localFiniteCharacter K P.val.val x * λ₀ v := by
  let xs : (Q : T) → Q.val.val.adicCompletion K := Pi.single P x
  have hx : sourceKPExteriorUpperTuple K hζ S₀ T xs =
      Pi.mulSingle P (sourceFiniteKP2ProjectiveLift K hζ P.val.val (sourceGL2Upper x)) := by
    funext Q
    by_cases hQP : Q = P
    · subst Q
      simp only [sourceKPExteriorUpperTuple, xs, Pi.single_eq_same, Pi.mulSingle_eq_same]
    · simp only [sourceKPExteriorUpperTuple, xs, Pi.single_eq_of_ne hQP, Pi.mulSingle_eq_of_ne hQP,
        sourceFiniteKP2ProjectiveLift_upper_zero]
  have hprod : (∏ Q : T, localFiniteCharacter K Q.val.val (xs Q)) = localFiniteCharacter K P.val.val x := by
    rw [Finset.prod_eq_single P]
    · simp only [xs, Pi.single_eq_same]
    · intro Q _ hQP
      rw [show xs Q = 0 by simp only [xs, Pi.single_eq_of_ne hQP], AddChar.map_zero_eq_one]
    · intro h
      exact (h (Finset.mem_univ P)).elim
  simpa only [hx, hprod] using sourceKPExteriorTensorWhittaker_upper K hζ S₀ T hS xs v

end
end ArtinMatthews
