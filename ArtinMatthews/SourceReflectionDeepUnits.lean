module

public import ArtinMatthews.SourceReflectionExteriorIdele
public import ArtinMatthews.VaryingKummerAnalyticRayIdealModulus
public import Mathlib.Topology.Algebra.Group.Neighborhood


set_option backward.privateInPublic true
@[expose] public section

/-! Deep units are the literal product of the original finite-place
higher-unit subgroups. Triviality there yields continuity. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain RayClass SourcePhysical
open scoped NumberField Topology

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

def sourceReflectionDeepUnits (n : FiniteModulus F) : Subgroup (SFiniteUnits F S) :=
  Subgroup.pi Set.univ fun P : S => localHigherUnitGroup P.val (n P.val)

theorem sourceReflectionDeepUnits_mem_iff (n : FiniteModulus F) (u : SFiniteUnits F S) :
    u ∈ sourceReflectionDeepUnits F S n ↔
      ∀ P : S, u P ∈ localHigherUnitGroup P.val (n P.val) := by
  simp [sourceReflectionDeepUnits, Subgroup.mem_pi]

theorem sourceReflectionDeepUnits_isOpen (n : FiniteModulus F) :
    IsOpen (sourceReflectionDeepUnits F S n : Set (SFiniteUnits F S)) := by
  change IsOpen (Set.univ.pi fun P : S => (localHigherUnitGroup P.val (n P.val) :
    Set (P.val.adicCompletion F)ˣ))
  exact isOpen_set_pi Set.finite_univ fun P _ => isOpen_localHigherUnitGroup P.val (n P.val)

theorem sourceReflectionDeepUnits_antitone {n m : FiniteModulus F} (h : n ≤ m) :
    sourceReflectionDeepUnits F S m ≤ sourceReflectionDeepUnits F S n := by
  intro u hu
  rw [sourceReflectionDeepUnits_mem_iff] at hu ⊢
  exact fun P => localHigherUnitGroup_antitone P.val (h P.val) (hu P)

theorem sourceReflectionCharacter_continuous_of_deep (n : FiniteModulus F)
    (χ : SFiniteUnits F S →* ℂˣ) (hχ : ∀ u ∈ sourceReflectionDeepUnits F S n, χ u = 1) :
    Continuous χ := by
  apply continuous_of_tendsto_nhds_one χ
  apply tendsto_const_nhds.congr'
  filter_upwards [(sourceReflectionDeepUnits_isOpen F S n).mem_nhds
    (sourceReflectionDeepUnits F S n).one_mem] with u hu
  exact (hχ u hu).symm

theorem sourceReflectionFiniteIdele_mem_ray_of_deep (n : FiniteModulus F)
    (u : SFiniteUnits F S) (hu : u ∈ sourceReflectionDeepUnits F S n) :
    sourceReflectionFiniteIdele F S u ∈ (Modulus.ofFinite n).ideleCongruenceSubgroup := by
  refine ⟨?_,?_⟩
  · change (1 : InfiniteIdeleGroup F) ∈ (Modulus.ofFinite n).infiniteCongruenceSubgroup
    exact Subgroup.one_mem _
  · intro P
    change (sourceReflectionFiniteIdele F S u).2 P ∈ localHigherUnitGroup P (n P)
    by_cases hP : P ∈ S
    · rw [sourceReflectionFiniteIdele_apply_mem F S u ⟨P,hP⟩]
      exact (sourceReflectionDeepUnits_mem_iff F S n u).mp hu ⟨P,hP⟩
    · rw [sourceReflectionFiniteIdele_apply_notMem F S u P hP]
      exact (localHigherUnitGroup P _).one_mem

theorem sourceReflectionPrincipalIdele_mem_primeTo_of_deep (n : FiniteModulus F)
    (hS : n.support ⊆ S) (a : Fˣ)
    (ha : sourceReflectionFiniteDiagonal F S a ∈ sourceReflectionDeepUnits F S n) :
    IdeleGroup.principalIdele F a ∈ idelePrimeToModulusSubgroup (Modulus.ofFinite n) := by
  refine ⟨?_,?_⟩
  · apply (Modulus.mem_infiniteCongruenceSubgroup_iff _ _).mpr
    simp [Modulus.ofFinite]
  · intro P hP
    have hPS : P ∈ S := hS hP
    change (IdeleGroup.principalIdele F a).2 P ∈ localHigherUnitGroup P (n P)
    rw [← sourceReflectionFiniteDiagonal_apply F S a ⟨P,hPS⟩]
    exact (sourceReflectionDeepUnits_mem_iff F S n _).mp ha ⟨P,hPS⟩

end
end ArtinMatthews.VaryingKummerAnalytic
