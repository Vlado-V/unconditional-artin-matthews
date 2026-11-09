module

public import ArtinMatthews.SourceKPAdelicRootSupportDecomposition
public import ArtinMatthews.SourceKPFiniteLevel


set_option backward.privateInPublic true
@[expose] public section

/-! A prescribed finite-cover lift and its matrix coordinates determine
the finite support factors, with the actual remaining central phase. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField AdeleRing MatrixGroups Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "F" => SourceKPFiniteAdeleCover K hζ
local notation "M" => sourceKPFiniteAdeleProjectiveMk K hζ
local notation "p" => sourceKPFiniteAdeleProjection K hζ
local notation "ev" => sourceKPAdeleMatrixAt K
local notation "prod" => sourceKPAdelicRootSupportProduct K hζ
local notation "tuple" => sourceKPAdelicRootSupportTuple K hζ

theorem sourceKPAdelicRootSupport_decomposition_of_lift
    (a : F) (S V : Finset Pr) (hSV : S ⊆ V)
    (h6 : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal → P ∈ V)
    (hout : ∀ P ∉ V, SourceKPIntegralMatrix (sourceKPFiniteVal K P) (ev P a.base)) :
    ∃ (z : rootsOfUnity 3 K) (k : sourceKPFiniteDeepMatrixGroup K),
      M a = sourceKPFiniteAdeleProjectiveCenter K hζ z *
        ((tuple 1 a.base S).2 * (tuple 1 a.base (V \ S)).2) * sourceKPFiniteLevelLift K hζ k := by
  let u := prod a.base V
  let r := u⁻¹*a
  have hr (P : Pr) : ev P r.base = if P ∈ V then 1 else ev P a.base := by
    change ev P (p (u⁻¹*a)) = _
    rw [map_mul p,map_inv p,map_mul (ev P),map_inv (ev P)]
    dsimp only [u]
    rw [sourceKPAdelicRootSupportProduct_at K hζ a.base V P]
    change (if P ∈ V then ev P a.base else 1)⁻¹ * ev P a.base = _
    by_cases hP : P ∈ V <;> simp [hP]
  have hk : r.base ∈ sourceKPFiniteDeepMatrixGroup K := by
    apply (sourceKPFiniteDeepMatrixGroup_mem K _).mpr
    constructor
    · intro P
      by_cases hP : P ∈ V
      · rw [hr P,ite_eq_left hP]
        exact (sourceKPIntegralMatrixMap_mem_range K P 1).mp ⟨1,map_one _⟩
      · rw [hr P,ite_eq_right hP]
        exact hout P hP
    · intro P hP
      rw [hr P,ite_eq_left (h6 P hP)]
      exact (sourceKPDeepLocalBase K P).range.one_mem
  let k : sourceKPFiniteDeepMatrixGroup K := ⟨r.base,hk⟩
  let z := sourceKPFiniteAdeleCenter K hζ r.central
  let v : F := ⟨1,r.base⟩
  have hz : z*v = r := by
    apply SourceKPFiniteAdeleCover.ext K hζ
    · change r.central*1*sourceKPAdeleMultiplier K hζ 1 r.base = r.central
      rw [sourceKPAdeleMultiplier_one_left,mul_one,mul_one]
    · exact one_mul r.base
  have hu : u = prod a.base S * prod a.base (V \ S) := by
    change prod a.base V = _
    calc
      _ = prod a.base (S ∪ (V \ S)) := congrArg (prod a.base) (Finset.union_sdiff_of_subset hSV).symm
      _ = _ := sourceKPAdelicRootSupportProduct_union K hζ a.base S (V \ S) Finset.disjoint_sdiff
  have ha : a = z * (prod a.base S * prod a.base (V \ S)) * v := by
    calc
      a = u*r := (mul_inv_cancel_left u a).symm
      _ = u*(z*v) := congrArg (fun b => u*b) hz.symm
      _ = z*u*v := by rw [← mul_assoc,(sourceKPFiniteAdeleCenter_commute K hζ r.central u).eq.symm]
      _ = _ := by rw [hu]
  refine ⟨r.central,k,?_⟩
  have hlevel : sourceKPFiniteLevelLift K hζ k = M v :=
    congrArg Prod.snd (sourceKPAdelicRootSupportDeepLift_eq K hζ k)
  rw [hlevel]
  change M a = M z * (M (prod a.base S) * M (prod a.base (V \ S))) * M v
  simpa only [map_mul] using congrArg M ha

end
end ArtinMatthews
