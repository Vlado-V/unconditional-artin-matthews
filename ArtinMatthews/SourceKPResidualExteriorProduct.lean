module

public import ArtinMatthews.SourceKPResidualTameFactor
public import ArtinMatthews.SourceKPAdelicRootSupportDecomposition


set_option backward.privateInPublic true
@[expose] public section

/-! The actual normalized residual coefficient separates every finite
exterior product from the fixed retained set. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup StandardAdelic
open SourcePhysical QuadraticWeil
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
local notation "ev" => sourceKPAdeleMatrixAt K

def sourceKPResidualExteriorFactor (a : A) (P : Pr) : ℂ :=
  if hP : P ∉ S then
    sourceKPTameCyclicWhittakerValue K hζ S₀ ⟨P,hP⟩ hS
      (sourceFiniteKP2ProjectiveLift K hζ P (ev P a))
  else 1

set_option maxRecDepth 4096 in
theorem sourceKPResidualFourierValue_exterior_product
    {T : ℝ} (hT : 2 < T) (a : A) (U : Finset Pr) (hUS : Disjoint U S) :
    sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le)
        ((tuple 1 a S).2 * (tuple 1 a U).2) =
      sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) (tuple 1 a S).2 *
        ∏ P ∈ U, sourceKPResidualExteriorFactor K hζ S₀ hS a P := by
  let W := sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le)
  induction U using Finset.induction_on with
  | empty =>
    have h : (tuple 1 a ∅).2 = 1 := by
      change sourceKPFiniteAdeleProjectiveMk K hζ (sourceKPAdelicRootSupportProduct K hζ a ∅) = 1
      rw [show sourceKPAdelicRootSupportProduct K hζ a (∅ : Finset Pr) = 1 from rfl,map_one]
    rw [h,mul_one,Finset.prod_empty,mul_one]
  | @insert P U hPU ih =>
    have hPS : P ∉ S :=
      fun h => (Finset.disjoint_left.mp hUS) (Finset.mem_insert_self _ _) h
    have hUS' : Disjoint U S := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hUS
    let g := sourceFiniteKP2ProjectiveLift K hζ P (ev P a)
    let qf := (tuple 1 a S).2 * (tuple 1 a U).2
    have hqf : sourceKPAdelicLocalBase K hζ P (1,qf) = 1 := by
      have hq : ((1,qf) : SourceKPAdelicProjective K hζ) = tuple 1 a S * tuple 1 a U := by
        apply Prod.ext
        · change 1 = (1 : PGL(2, InfiniteAdeleRing K))*1
          exact (one_mul _).symm
        · rfl
      rw [hq,map_mul,sourceKPAdelicRootSupportTuple_at_of_not_mem K hζ 1 a S P hPS,
        sourceKPAdelicRootSupportTuple_at_of_not_mem K hζ 1 a U P hPU,mul_one]
    have htuple : (tuple 1 a (insert P U)).2 =
        (tuple 1 a U).2 * (sourceKPAdelicLocalProjective K hζ P g).2 := by
      exact congrArg Prod.snd (sourceKPAdelicRootSupportTuple_insert K hζ 1 a U P hPU)
    have hW := sourceKPTameResidualFourierValue_factor K hζ S₀ ⟨P,hPS⟩ hS hT qf hqf g
    have hI : W qf = W (tuple 1 a S).2 * ∏ Q ∈ U, sourceKPResidualExteriorFactor K hζ S₀ hS a Q :=
      ih hUS'
    have hF : sourceKPResidualExteriorFactor K hζ S₀ hS a P =
        sourceKPTameCyclicWhittakerValue K hζ S₀ ⟨P,hPS⟩ hS g := dite_eq_left hPS
    have harg : (tuple 1 a S).2 * (tuple 1 a (insert P U)).2 =
        qf * (sourceKPAdelicLocalProjective K hζ P g).2 := by
      rw [htuple]
      exact (mul_assoc (tuple 1 a S).2 (tuple 1 a U).2
        ((sourceKPAdelicLocalProjective K hζ P g).2 : Gf)).symm
    calc
      _ = W (qf * (sourceKPAdelicLocalProjective K hζ P g).2) := congrArg W harg
      _ = W qf * sourceKPTameCyclicWhittakerValue K hζ S₀ ⟨P,hPS⟩ hS g := by
        dsimp only [W]
        exact hW
      _ = _ := by
        rw [hI, Finset.prod_insert hPU, hF]
        ring

end
end ArtinMatthews
