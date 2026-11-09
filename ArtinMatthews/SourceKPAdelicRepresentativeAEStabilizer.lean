module

public import ArtinMatthews.SourceKPAdelicUpperAE


set_option backward.privateInPublic true
@[expose] public section

/-! The full representative Haar measure is preserved by the actual cover
action, so almost-everywhere invariance is closed under group operations. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Filter
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "G" => SourceKPAdelicProjective K hζ
local notation "X" => SourceKPFiniteLevelSpace K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "Q" => sourceKPFiniteLevelToCompact K hζ
local notation "ν" => sourceKPFiniteRepresentativeHaar K hζ
local notation "R" => sourceKPAdelicProjectiveRationalLift K hζ
local notation "N" => sourceKPAdelicUpperLift K hζ
local notation "w" => sourceKPAdelicProjectiveWeyl K hζ

def sourceKPAdelicRepresentativeAEStabilizer {B : Type*} (f : X → B) : Subgroup G where
  carrier := {g | ∀ᵐ x ∂ν, f (g • x) = f x}
  one_mem' := ae_of_all _ fun x => congrArg f (one_smul G x)
  mul_mem' {g h} hg hh := by
    change (∀ᵐ x ∂ν, f (g • x) = f x) at hg
    change (∀ᵐ x ∂ν, f (h • x) = f x) at hh
    change ∀ᵐ x ∂ν, f ((g*h) • x) = f x
    have hm : MeasurePreserving (fun x : X => h • x) ν ν :=
      sourceKPFiniteRepresentativeHaar_left K hζ h
    have hshift := hm.quasiMeasurePreserving.ae hg
    filter_upwards [hshift, hh] with x hx hy
    rw [mul_smul]
    exact hx.trans hy
  inv_mem' {g} hg := by
    change (∀ᵐ x ∂ν, f (g • x) = f x) at hg
    change ∀ᵐ x ∂ν, f (g⁻¹ • x) = f x
    have hm : MeasurePreserving (fun x : X => g⁻¹ • x) ν ν :=
      sourceKPFiniteRepresentativeHaar_left K hζ g⁻¹
    have hshift := hm.quasiMeasurePreserving.ae hg
    filter_upwards [hshift] with x hx
    change f (g • (g⁻¹ • x)) = f (g⁻¹ • x) at hx
    change f (g⁻¹ • x) = f x
    rw [smul_inv_smul] at hx
    exact hx.symm

abbrev sourceKPAutomorphicCompactAEStabilizer {B : Type*} (W : Y → B) : Subgroup G :=
  sourceKPAdelicRepresentativeAEStabilizer K hζ (W ∘ Q)

local notation "S[" W "]" => sourceKPAutomorphicCompactAEStabilizer K hζ W

theorem sourceKPAutomorphicCompactAEStabilizer_mem_iff {B : Type*} (W : Y → B) (g : G) :
    g ∈ S[W] ↔ ∀ᵐ x ∂ν, W (Q (g • x)) = W (Q x) := Iff.rfl

theorem sourceKPAutomorphicCompactAEStabilizer_mem_rational {B : Type*} (W : Y → B)
    (γ : PGL(2, K)) : R γ ∈ S[W] :=
  ae_of_all _ fun x => congrArg W (sourceKPFiniteLevelToCompact_rational K hζ γ x)

theorem sourceKPAutomorphicCompactAEStabilizer_upper_le {B : Type*} (W : Y → B)
    (hN : ∀ u : 𝔸[K], ∀ᵐ x ∂ν, W (Q (N u • x)) = W (Q x)) :
    (sourceKPAdelicUpperHom K hζ).range ≤ S[W] := by
  rintro _ ⟨u,rfl⟩
  exact hN u.toAdd

theorem sourceKPAutomorphicCompactAEStabilizer_mem_weyl {B : Type*} (W : Y → B) :
    w ∈ S[W] :=
  sourceKPAutomorphicCompactAEStabilizer_mem_rational K hζ W
    (ProjGenLinGroup.mk (sourceKPWeylMatrix K))

theorem sourceKPAutomorphicCompactAEStabilizer_mem_weyl_conj_upper {B : Type*} (W : Y → B)
    (u : 𝔸[K]) (hu : N u ∈ S[W]) :
    w * N u * w⁻¹ ∈ S[W] := by
  have hw := sourceKPAutomorphicCompactAEStabilizer_mem_weyl K hζ W
  exact (S[W]).mul_mem ((S[W]).mul_mem hw hu) ((S[W]).inv_mem hw)

end
end ArtinMatthews
