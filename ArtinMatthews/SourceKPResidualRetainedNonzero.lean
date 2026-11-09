module

public import ArtinMatthews.SourceKPResidualExteriorProduct
public import ArtinMatthews.SourceKPCuspResidualFourierSymmetries
public import ArtinMatthews.SourceKPResidualUnitNonzero
public import ArtinMatthews.SourceKPAdelicRootWildPlace


set_option backward.privateInPublic true
@[expose] public section

/-! The nonzero unit coefficient can be placed on the original retained
set by removing every exterior local factor and the actual level factor. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix StandardAdelic QuadraticWeil
open scoped NumberField AdeleRing MatrixGroups Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "S" => sourceHilbertSet K S₀
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "tuple" => sourceKPAdelicRootSupportTuple K hζ

theorem sourceKPResidualFourierValue_fixed_support
    {T : ℝ} (hT : 2 < T) (qf : Gf) :
    ∃ (a : A) (U : Finset Pr) (z : rootsOfUnity 3 K) (k : sourceKPFiniteDeepMatrixGroup K),
      Disjoint U S ∧
      qf = sourceKPFiniteAdeleProjectiveCenter K hζ z *
        ((tuple 1 a S).2 * (tuple 1 a U).2) * sourceKPFiniteLevelLift K hζ k ∧
      sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) qf =
        (sourceKPAdelicCentralComplex K hζ z : ℂ) *
          sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) (tuple 1 a S).2 *
          ∏ P ∈ U, sourceKPResidualExteriorFactor K hζ S₀ hS a P := by
  obtain ⟨a,V,z,k,_,_,_,_,_,he⟩ := sourceKPAdelicRootSupport_decomposition K hζ
    ((1,qf) : SourceKPAdelicProjective K hζ) S
  let U := V \ S
  have hU : Disjoint U S := Finset.sdiff_disjoint
  have hq : qf = sourceKPFiniteAdeleProjectiveCenter K hζ z *
      ((tuple 1 a.base S).2 * (tuple 1 a.base U).2) * sourceKPFiniteLevelLift K hζ k := by
    have hf := congrArg Prod.snd he
    change qf = sourceKPFiniteAdeleProjectiveCenter K hζ z *
      (tuple 1 a.base S).2 * (tuple 1 a.base U).2 * sourceKPFiniteLevelLift K hζ k at hf
    exact hf.trans (congrArg (fun b : Gf => b * sourceKPFiniteLevelLift K hζ k) (mul_assoc _ _ _))
  refine ⟨a.base,U,z,k,hU,hq,?_⟩
  rw [hq,sourceKPCuspResidualFourierValue_right_deep,
    sourceKPCuspResidualFourierValue_center,
    sourceKPResidualFourierValue_exterior_product K hζ S₀ hS hT a.base U hU]
  rw [mul_assoc]

include hS in
theorem sourceKPResidualFourierValue_retained_ne_zero_of
    {T : ℝ} (hT : 2 < T) (qf : Gf)
    (hqf : sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) qf ≠ 0) :
    ∃ a : A, sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le)
      (tuple 1 a S).2 ≠ 0 := by
  obtain ⟨a,U,z,k,hU,hg,hW⟩ := sourceKPResidualFourierValue_fixed_support K hζ S₀ hS hT qf
  refine ⟨a,fun hz => hqf ?_⟩
  rw [hW,hz,mul_zero,zero_mul]

include hS in
theorem sourceKPResidualFourierValue_retained_exists_ne_zero
    {T : ℝ} (hT : 2 < T) :
    ∃ a : A, sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le)
      (tuple 1 a S).2 ≠ 0 := by
  obtain ⟨P,hP⟩ := sourceKPAdelicRoot_exists_wild_place K
  obtain ⟨qf,hqf⟩ := sourceKPCuspResidualFourierValue_unit_exists_ne_zero K hζ P
    (one_le_two.trans hT.le)
  exact sourceKPResidualFourierValue_retained_ne_zero_of K hζ S₀ hS hT qf hqf

end
end ArtinMatthews
