module

public import ArtinMatthews.SourceKPResidualPrincipalLift
public import ArtinMatthews.SourceKPResidualExteriorProduct
public import ArtinMatthews.SourceKPCuspResidualFourierSymmetries
public import ArtinMatthews.SourceKPResidualUnitNormalization
public import ArtinMatthews.SourceKPExteriorWhittakerProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The actual residual Fourier coefficient on a prescribed retained
vector has the literal squarefree-cube Gamma-two factor. The remaining
phase and finite fibre retain their original cover data. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix StandardAdelic QuadraticWeil VaryingKummerAnalytic
open scoped NumberField AdeleRing MatrixGroups Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "S" => sourceHilbertSet K S₀
local notation "D" => SourcePrimeExponents K S₀
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "tuple" => sourceKPAdelicRootSupportTuple K hζ
local notation "rD" => fun m : Kˣ => Prod.snd (sourceKPAdelicProjectiveRationalLift K hζ
  (sourceKPProjectiveDiagonalHom K m))

include hS in
/-- The exterior coefficient retains directed CRT and permits shared
prime divisors of the squarefree and cube factors. -/
theorem sourceKPResidualFourierValue_principal_squarefree_cube
    {T : ℝ} (hT : 2 < T) (a : A) (c : ReflectionSquarefreeExponents K S₀) (n : D) :
    let m := sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n)
    let b := sourceKPResidualPrincipalFiniteLift K hζ S₀ m a
    ∃ z : rootsOfUnity 3 K,
      sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) (rD m * (tuple 1 a S).2) =
        (sourceKPAdelicCentralComplex K hζ z : ℂ) *
          sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) (tuple 1 b.base S).2 *
          (reflectionGammaTwo K hζ S₀ c.val /
            ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) * (sourcePrimeExponentNorm K S₀ n : ℂ))) := by
  let e := c.val + 3 • n
  let m := sourcePrimeExponentUnit K hζ S₀ e
  let b := sourceKPResidualPrincipalFiniteLift K hζ S₀ m a
  let C := c.val.support ∪ n.support
  let U : Finset Pr := C.image Subtype.val
  let V := S ∪ U
  have hUS : Disjoint U S := by
    apply Finset.disjoint_left.mpr
    intro P hP hS'
    obtain ⟨Q,_,rfl⟩ := Finset.mem_image.mp hP
    exact Q.property hS'
  have h6 (P : Pr) (hP : (6 : 𝓞 K) ∈ P.asIdeal) : P ∈ V := by
    have hPS : P ∈ S := by
      by_contra hn
      exact source_exterior_six_not_mem K S₀ P hn hP
    exact Finset.mem_union_left _ hPS
  have hout (P : Pr) (hP : P ∉ V) :
      SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPAdeleMatrixAt K P b.base) := by
    have hPS : P ∉ S := fun h => hP (Finset.mem_union_left _ h)
    have hPC : (⟨P,hPS⟩ : SourceExteriorPrime K S₀) ∉ C :=
      fun h => hP (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨P,hPS⟩,h,rfl⟩))
    have hc : c.val ⟨P,hPS⟩ = 0 :=
      Finsupp.notMem_support_iff.mp (fun h => hPC (Finset.mem_union_left _ h))
    have hn : n ⟨P,hPS⟩ = 0 :=
      Finsupp.notMem_support_iff.mp (fun h => hPC (Finset.mem_union_right _ h))
    apply sourceKPResidualPrincipalFiniteLift_exterior_integral K hζ S₀ a e ⟨P,hPS⟩
    simp only [e,Finsupp.add_apply,Finsupp.smul_apply,hc,hn,smul_zero,add_zero]
  obtain ⟨z,k,hq⟩ := sourceKPAdelicRootSupport_decomposition_of_lift K hζ b S V
    Finset.subset_union_left h6 hout
  have hV : V \ S = U := by
    ext P
    simp only [V,Finset.mem_sdiff,Finset.mem_union]
    constructor
    · rintro ⟨h,hP⟩
      exact h.resolve_left hP
    · exact fun h => ⟨Or.inr h, fun hS' => (Finset.disjoint_left.mp hUS) h hS'⟩
  rw [hV] at hq
  have hprod : (∏ P ∈ U, sourceKPResidualExteriorFactor K hζ S₀ hS b.base P) =
      reflectionGammaTwo K hζ S₀ c.val /
        ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) * (sourcePrimeExponentNorm K S₀ n : ℂ)) := by
    change (∏ P ∈ C.image Subtype.val, sourceKPResidualExteriorFactor K hζ S₀ hS b.base P) = _
    rw [Finset.prod_image (fun P _ Q _ h => Subtype.ext h)]
    calc
      _ = ∏ P ∈ C, sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS m := by
        apply Finset.prod_congr rfl
        intro P _
        rw [sourceKPResidualExteriorFactor,dite_eq_left P.property,
          sourceKPResidualPrincipalFiniteLift_exterior K hζ S₀ m a P]
        rfl
      _ = _ := sourceKPTameExteriorWhittakerProduct_squarefree_cube K hζ S₀ hS c n C
        Finset.subset_union_left Finset.subset_union_right
  refine ⟨z,?_⟩
  change sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le)
    (rD m * (tuple 1 a S).2) = _
  rw [← sourceKPResidualPrincipalFiniteLift_mk K hζ S₀ m a,hq,
    sourceKPCuspResidualFourierValue_right_deep,sourceKPCuspResidualFourierValue_center,
    sourceKPResidualFourierValue_exterior_product K hζ S₀ hS hT b.base U hUS,hprod,mul_assoc]

end
end ArtinMatthews
