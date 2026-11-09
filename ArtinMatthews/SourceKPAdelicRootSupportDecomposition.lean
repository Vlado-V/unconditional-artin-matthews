module

public import ArtinMatthews.SourceKPAdelicRootSupportProduct
public import ArtinMatthews.SourceFiniteProjectiveSupport
public import ArtinMatthews.SourceKPFiniteSmoothSection
public import ArtinMatthews.SourceKPLocalRestBase


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed retained set is kept fixed when factoring an actual
adelic cover element. The additional local factors are finite and
exterior to that set. A single genuine central phase and the actual
fixed compact level account for the entire remaining factor. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "F" => SourceKPFiniteAdeleCover K hζ
local notation "G" => SourceKPAdelicProjective K hζ
local notation "G∞" => PGL(2, InfiniteAdeleRing K)
local notation "M" => sourceKPFiniteAdeleProjectiveMk K hζ
local notation "p" => sourceKPFiniteAdeleProjection K hζ
local notation "ev" => sourceKPAdeleMatrixAt K
local notation "prod" => sourceKPAdelicRootSupportProduct K hζ
local notation "J" => sourceKPFiniteDeepMatrixGroup K
local notation "k₀" => sourceKPFiniteDeepCoverLift K hζ
local notation "z₀" => sourceKPAdelicProjectiveCenter K hζ

def sourceKPAdelicRootSupportTuple (u : G∞) (a : A) (T : Finset Pr) : G :=
  (u,M (prod a T))

local notation "tuple" => sourceKPAdelicRootSupportTuple K hζ

theorem sourceKPAdelicRootSupportTuple_at_of_not_mem (u : G∞) (a : A) (T : Finset Pr)
    (P : Pr) (hP : P ∉ T) : sourceKPAdelicLocalBase K hζ P (tuple u a T) = 1 := by
  change ProjGenLinGroup.mk (ev P (p (prod a T))) = 1
  rw [sourceKPAdelicRootSupportProduct_at_of_not_mem K hζ a T P hP, map_one]

theorem sourceKPAdelicRootSupportTuple_insert (u : G∞) (a : A) (T : Finset Pr)
    (P : Pr) (hP : P ∉ T) :
    tuple u a (insert P T) = tuple u a T *
      sourceKPAdelicLocalProjective K hζ P (sourceFiniteKP2ProjectiveLift K hζ P (ev P a)) := by
  let g := sourceFiniteKP2ProjectiveLift K hζ P (ev P a)
  have he : tuple u a (insert P T) = sourceKPAdelicLocalProjective K hζ P g * tuple u a T := by
    apply Prod.ext
    · change u = 1*u
      rw [one_mul]
    · change M (prod a (insert P T)) = M (sourceKPAdelicRootSupportFactor K hζ a P) * M (prod a T)
      rw [sourceKPAdelicRootSupportProduct_insert K hζ a T P hP, map_mul M]
  exact he.trans (sourceKPAdelicLocalProjective_commute_of_base_one K hζ P g (tuple u a T)
    (sourceKPAdelicRootSupportTuple_at_of_not_mem K hζ u a T P hP)).eq

theorem sourceKPAdelicRootSupportDeepLift_eq (k : J) :
    k₀ k = (1,M (⟨1,k.val⟩ : F)) := by
  rw [sourceKPFiniteDeepCoverLift_eq,sourceKPFiniteMatrixLift,sourceKPAdelicMatrixLift,
    sourceKPFiniteMatrixEmbedding_product,map_one]
  rfl

theorem sourceKPAdelicRootSupport_decomposition (g : G) (S : Finset Pr) :
    ∃ (a : F) (T : Finset Pr) (z : rootsOfUnity 3 K) (k : J),
      M a = g.2 ∧ S ⊆ T ∧
      StandardAdelic.traceBadPlaces K ⊆ T ∧
      (∀ P, (6 : 𝓞 K) ∈ P.asIdeal → P ∈ T) ∧
      (∀ P ∈ T, ev P k.val = 1) ∧
      g = z₀ z * tuple g.1 a.base S * tuple 1 a.base (T \ S) * k₀ k := by
  obtain ⟨a,T,ha,hST,hbad,houtside⟩ := sourceKPFiniteProjective_finite_support K hζ g.2 S
  have h6 (P : Pr) (hP : (6 : 𝓞 K) ∈ P.asIdeal) : P ∈ T := by
    by_contra h
    exact (houtside P h).1 hP
  let u := prod a.base T
  let r := u⁻¹*a
  have hr (P : Pr) : ev P r.base = if P ∈ T then 1 else ev P a.base := by
    change ev P (p (u⁻¹*a)) = _
    rw [map_mul p,map_inv p,map_mul (ev P),map_inv (ev P)]
    dsimp only [u]
    rw [sourceKPAdelicRootSupportProduct_at K hζ a.base T P]
    change (if P ∈ T then ev P a.base else 1)⁻¹ * ev P a.base = _
    by_cases hP : P ∈ T <;> simp [hP]
  have hdeep : r.base ∈ J := by
    apply (sourceKPFiniteDeepMatrixGroup_mem K _).mpr
    constructor
    · intro P
      by_cases hP : P ∈ T
      · rw [hr P,ite_eq_left hP]
        exact (sourceKPIntegralMatrixMap_mem_range K P 1).mp ⟨1,map_one _⟩
      · rw [hr P,ite_eq_right hP]
        exact (houtside P hP).2
    · intro P hP
      rw [hr P,ite_eq_left (h6 P hP)]
      exact (sourceKPDeepLocalBase K P).range.one_mem
  let k : J := ⟨r.base,hdeep⟩
  let z := sourceKPFiniteAdeleCenter K hζ r.central
  let v : F := ⟨1,r.base⟩
  have hrphase : z*v = r := by
    apply SourceKPFiniteAdeleCover.ext K hζ
    · change r.central*1*sourceKPAdeleMultiplier K hζ 1 r.base = r.central
      rw [sourceKPAdeleMultiplier_one_left,mul_one,mul_one]
    · exact one_mul r.base
  have hu : u = prod a.base S * prod a.base (T \ S) := by
    change prod a.base T = _
    calc
      _ = prod a.base (S ∪ (T \ S)) := congrArg (prod a.base) (Finset.union_sdiff_of_subset hST).symm
      _ = _ := sourceKPAdelicRootSupportProduct_union K hζ a.base S (T \ S) Finset.disjoint_sdiff
  have ha' : a = z * prod a.base S * prod a.base (T \ S) * v := by
    calc
      a = u*r := (mul_inv_cancel_left u a).symm
      _ = u*(z*v) := congrArg (fun w => u*w) hrphase.symm
      _ = z*u*v := by rw [← mul_assoc,(sourceKPFiniteAdeleCenter_commute K hζ r.central u).eq.symm]
      _ = _ := by rw [hu,← mul_assoc z]
  refine ⟨a,T,r.central,k,ha,hST,hbad,h6,fun P hP => ?_,?_⟩
  · change ev P r.base = 1
    rw [hr P,ite_eq_left hP]
  · rw [sourceKPAdelicRootSupportDeepLift_eq K hζ k]
    apply Prod.ext
    · change g.1 = 1*g.1*1*1
      rw [one_mul,mul_one,mul_one]
    · change g.2 = M z * M (prod a.base S) * M (prod a.base (T \ S)) * M v
      exact ha.symm.trans (by simpa only [map_mul] using congrArg M ha')

end
end ArtinMatthews
