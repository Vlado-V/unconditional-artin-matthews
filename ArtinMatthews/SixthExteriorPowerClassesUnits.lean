module

public import ArtinMatthews.SixthExteriorPowerClasses
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Noetherian.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine finite generation of exterior S-units. The finite-S valuation
map has the actual integral units as kernel. Dirichlet's unit theorem and
Noetherianity of the finite integer lattice give finite generation, without
an S-unit finite-generation or principal-ideal hypothesis. -/
namespace ArtinMatthews
open IsDedekindDomain
open scoped NumberField nonZeroDivisors
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def exteriorIntegralUnitEmbedding : (𝓞 K)ˣ →* Kˣ :=
  Units.map (algebraMap (𝓞 K) K).toMonoidHom

theorem exteriorIntegralUnit_principal (u : (𝓞 K)ˣ) :
    (toPrincipalIdeal (𝓞 K) K (exteriorIntegralUnitEmbedding u) :
      FractionalIdeal (𝓞 K)⁰ K)=1 := by
  rw [coe_toPrincipalIdeal,← FractionalIdeal.spanSingleton_one]
  apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
  refine ⟨u⁻¹,?_⟩
  change algebraMap (𝓞 K) K (↑(u⁻¹)) * algebraMap (𝓞 K) K (↑u)=1
  rw [← map_mul,Units.inv_mul,map_one]

@[simp] theorem exteriorPrincipalValuation_integralUnit (p : HeightOneSpectrum (𝓞 K))
    (u : (𝓞 K)ˣ) : exteriorPrincipalValuation p (exteriorIntegralUnitEmbedding u)=0 := by
  unfold exteriorPrincipalValuation
  rw [exteriorIntegralUnit_principal,FractionalIdeal.count_one]

/-- Zero exponents at all actual prime ideals mean that the principal
fractional ideal is one, hence the field unit comes from an integral unit. -/
theorem exteriorPrincipalValuation_all_zero_iff (u : Kˣ) :
    (∀ p : HeightOneSpectrum (𝓞 K), exteriorPrincipalValuation p u=0) ↔
      ∃ w : (𝓞 K)ˣ, exteriorIntegralUnitEmbedding w=u := by
  constructor
  · intro h
    have hp : (toPrincipalIdeal (𝓞 K) K u : FractionalIdeal (𝓞 K)⁰ K)=1 := by
      have hf := FractionalIdeal.finprod_heightOneSpectrum_factorization'
        (K := K) (toPrincipalIdeal (𝓞 K) K u).ne_zero
      have hc (p : HeightOneSpectrum (𝓞 K)) :
          FractionalIdeal.count K p (toPrincipalIdeal (𝓞 K) K u : FractionalIdeal (𝓞 K)⁰ K)=0 := h p
      simpa only [hc,zpow_zero,finprod_one] using hf.symm
    have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ (u:K)=
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (1:K) := by
      simpa only [coe_toPrincipalIdeal,FractionalIdeal.spanSingleton_one] using hp
    obtain ⟨w,hw⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hs
    have he : exteriorIntegralUnitEmbedding w*u=1 := by
      apply Units.ext
      exact hw
    refine ⟨w⁻¹,?_⟩
    have he' : exteriorIntegralUnitEmbedding w * exteriorIntegralUnitEmbedding (w⁻¹)=
        exteriorIntegralUnitEmbedding w*u := by
      rw [map_inv,mul_inv_cancel,he]
    exact mul_left_cancel he'
  · rintro ⟨w,rfl⟩ p
    exact exteriorPrincipalValuation_integralUnit p w

def exteriorIntegralUnitMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (𝓞 K)ˣ →* exteriorUnitSubgroup S where
  toFun u := ⟨exteriorIntegralUnitEmbedding u,by
    intro p _
    exact exteriorPrincipalValuation_integralUnit p u⟩
  map_one' := Subtype.ext (map_one exteriorIntegralUnitEmbedding)
  map_mul' u v := Subtype.ext (map_mul exteriorIntegralUnitEmbedding u v)

def exteriorSValuationAddHom (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Additive (exteriorUnitSubgroup S) →+ (S → ℤ) where
  toFun u p := exteriorPrincipalValuation p.1 (Additive.toMul u).1
  map_zero' := by
    funext p
    exact exteriorPrincipalValuation_one p.1
  map_add' u v := by
    funext p
    exact exteriorPrincipalValuation_mul p.1 (Additive.toMul u).1 (Additive.toMul v).1

def exteriorSValuationLinearMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Additive (exteriorUnitSubgroup S) →ₗ[ℤ] (S → ℤ) :=
  (exteriorSValuationAddHom S).toIntLinearMap

def exteriorIntegralUnitLinearMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Additive (𝓞 K)ˣ →ₗ[ℤ] Additive (exteriorUnitSubgroup S) :=
  (exteriorIntegralUnitMap S).toAdditive.toIntLinearMap

/-- The kernel is identified from actual principal ideals, not supplied
as an exactness assumption. -/
theorem exteriorSValuation_range_eq_ker (S : Finset (HeightOneSpectrum (𝓞 K))) :
    LinearMap.range (exteriorIntegralUnitLinearMap S)=LinearMap.ker (exteriorSValuationLinearMap S) := by
  ext u
  constructor
  · rintro ⟨w,rfl⟩
    change exteriorSValuationLinearMap S (exteriorIntegralUnitLinearMap S w)=0
    funext p
    exact exteriorPrincipalValuation_integralUnit p.1 (Additive.toMul w)
  · intro hu
    change exteriorSValuationLinearMap S u=0 at hu
    have hz : ∀ p : HeightOneSpectrum (𝓞 K), exteriorPrincipalValuation p (Additive.toMul u).1=0 := by
      intro p
      by_cases hp : p ∈ S
      · exact congrFun hu ⟨p,hp⟩
      · exact (Additive.toMul u).2 p hp
    obtain ⟨w,hw⟩ := (exteriorPrincipalValuation_all_zero_iff (Additive.toMul u).1).mp hz
    refine ⟨Additive.ofMul w,?_⟩
    change exteriorIntegralUnitMap S w=Additive.toMul u
    exact Subtype.ext hw

theorem exteriorUnit_moduleFinite (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Module.Finite ℤ (Additive (exteriorUnitSubgroup S)) := by
  classical
  rw [Module.finite_def]
  apply Submodule.fg_of_fg_map_of_fg_inf_ker (exteriorSValuationLinearMap S)
  · rw [Submodule.map_top]
    exact IsNoetherian.noetherian _
  · rw [inf_of_le_right le_top,← exteriorSValuation_range_eq_ker S]
    simpa only [Submodule.map_top] using
      (Module.Finite.fg_top (R := ℤ) (M := Additive (𝓞 K)ˣ)).map (exteriorIntegralUnitLinearMap S)

theorem exteriorUnit_fg (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Group.FG (exteriorUnitSubgroup S) := by
  rw [GroupFG.iff_add_fg,← Module.Finite.iff_addGroup_fg]
  exact exteriorUnit_moduleFinite S

end
end ArtinMatthews
