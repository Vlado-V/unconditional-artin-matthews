module

public import ArtinMatthews.SourceKPRetainedPrincipalTransport
public import ArtinMatthews.SourceKPRetainedExteriorDiagonal
public import ArtinMatthews.SourceKPResidualPrincipalCoefficient


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical squarefree-cube rational diagonal has the original
Gamma-two factor on the exterior. Its compact diagonal is an actual deep lift and the exterior split
has phase one. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix StandardAdelic QuadraticWeil VaryingKummerAnalytic
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "unitAt" => sourceKPRetainedUnitAt K
local notation "tuple" => sourceKPAdelicRootSupportTuple K hζ
local notation "ev" => sourceKPAdeleMatrixAt K
local notation "rUnit" => FiniteAdeleRing.unitEmbedding (𝓞 K) K

theorem sourceKPRetainedPrincipalExterior_squarefree_cube
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (c : ReflectionSquarefreeExponents K S₀) (n : SourcePrimeExponents K S₀) :
    let S := sourceHilbertSet K S₀
    let m := sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n)
    let b := sourceKPRetainedExteriorUnitPart K S (rUnit m)
    let A₀ := sourceKPDiagonalHom 𝔸ᶠ[K] b
    let U : Finset Pr := (c.val.support ∪ n.support).image Subtype.val
    ∃ k : sourceKPFiniteDeepMatrixGroup K,
      Disjoint U S ∧
      D b = (tuple 1 A₀ U).2 * sourceKPFiniteLevelLift K hζ k ∧
      (∏ P ∈ U, sourceKPResidualExteriorFactor K hζ S₀ hS A₀ P) =
        reflectionGammaTwo K hζ S₀ c.val /
          ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) *
            (sourcePrimeExponentNorm K S₀ n : ℂ)) := by
  let S := sourceHilbertSet K S₀
  let e := c.val + 3 • n
  let m := sourcePrimeExponentUnit K hζ S₀ e
  let b := sourceKPRetainedExteriorUnitPart K S (rUnit m)
  let A₀ := sourceKPDiagonalHom 𝔸ᶠ[K] b
  let C := c.val.support ∪ n.support
  let U : Finset Pr := C.image Subtype.val
  have hUS : Disjoint U S := by
    apply Finset.disjoint_left.mpr
    intro P hP hS'
    obtain ⟨Q,_,rfl⟩ := Finset.mem_image.mp hP
    exact Q.property hS'
  have hext (P : Pr) (hP : P ∉ S) : ev P A₀ =
      sourceGL2Diagonal (Units.map (algebraMap K (P.adicCompletion K)).toMonoidHom m) := by
    dsimp only [A₀]
    rw [sourceKPAdeleMatrixAt_diagonal]
    change sourceGL2Diagonal (unitAt P b) = _
    rw [sourceKPRetainedExteriorUnitPart_unitAt_notMem K S (rUnit m) P hP,
      sourceKPRetainedUnitAt_rational]
  have hret (P : Pr) (hP : P ∈ S) : ev P A₀ = 1 := by
    dsimp only [A₀]
    rw [sourceKPAdeleMatrixAt_diagonal]
    change sourceGL2Diagonal (unitAt P b) = _
    rw [sourceKPRetainedExteriorUnitPart_unitAt_mem K S (rUnit m) ⟨P,hP⟩,
      ← sourceKPDiagonalHom_field, map_one]
  have h6 (P : Pr) (hP : (6 : 𝓞 K) ∈ P.asIdeal) : ev P A₀ = 1 := by
    apply hret
    by_contra hn
    exact source_exterior_six_not_mem K S₀ P hn hP
  have hout (P : Pr) (hP : P ∉ U) : SourceKPIntegralMatrix (sourceKPFiniteVal K P) (ev P A₀) := by
    by_cases hPS : P ∈ S
    · rw [hret P hPS]
      exact (sourceKPIntegralMatrixMap_mem_range K P 1).mp ⟨1,map_one _⟩
    have hPC : (⟨P,hPS⟩ : SourceExteriorPrime K S₀) ∉ C :=
      fun h => hP (Finset.mem_image.mpr ⟨⟨P,hPS⟩,h,rfl⟩)
    have hc : c.val ⟨P,hPS⟩ = 0 :=
      Finsupp.notMem_support_iff.mp (fun h => hPC (Finset.mem_union_left _ h))
    have hn : n ⟨P,hPS⟩ = 0 :=
      Finsupp.notMem_support_iff.mp (fun h => hPC (Finset.mem_union_right _ h))
    change SourceKPIntegralMatrix (sourceKPFiniteVal K P) (ev P A₀)
    rw [hext P hPS, ← sourceKPResidualPrincipalFiniteLift_exterior K hζ S₀ m A₀ ⟨P,hPS⟩]
    apply sourceKPResidualPrincipalFiniteLift_exterior_integral K hζ S₀ A₀ e ⟨P,hPS⟩
    simp only [e,Finsupp.add_apply,Finsupp.smul_apply,hc,hn,smul_zero,add_zero]
  obtain ⟨k,hk⟩ := sourceKPRetainedDiagonalLift_eq_tuple_mul_level K hζ U b h6 hout
  refine ⟨k,hUS,hk,?_⟩
  change (∏ P ∈ C.image Subtype.val, sourceKPResidualExteriorFactor K hζ S₀ hS A₀ P) = _
  rw [Finset.prod_image (fun P _ Q _ h => Subtype.ext h)]
  calc
    _ = ∏ P ∈ C, sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS m := by
      apply Finset.prod_congr rfl
      intro P _
      rw [sourceKPResidualExteriorFactor, dite_eq_left P.property, hext P.val P.property]
      rfl
    _ = _ := sourceKPTameExteriorWhittakerProduct_squarefree_cube K hζ S₀ hS c n C
      Finset.subset_union_left Finset.subset_union_right

end
end ArtinMatthews
