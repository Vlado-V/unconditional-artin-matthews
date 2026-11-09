module

public import ArtinMatthews.SourceKPTranslateCompactHaarCenter
public import ArtinMatthews.SourceKPTranslateCompactL2
public import ArtinMatthews.SourceKPCompactGenuineL2


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine Haar L² retains its forward cubic character on the actual common level. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "Z" => rootsOfUnity 3 K
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T
local notation "μJ" => sourceKPTranslateCompactHaar K hζ T

theorem sourceKPTranslateCompactPullbackL2_genuine (t : Gf) (h : J ≤ D t)
    (f : SourceKPGenuineAutomorphicL2 K hζ) (z : Z) :
    (fun x : YJ => sourceKPTranslateCompactPullbackL2 K hζ T t h f.val (z • x)) =ᵐ[μJ]
      fun x => (sourceKPAdelicCentralComplex K hζ z : ℂ) *
        sourceKPTranslateCompactPullbackL2 K hζ T t h f.val x := by
  let p := sourceKPTranslateAutomorphicCompactMap K hζ T t h
  let F := sourceKPTranslateCompactPullbackL2 K hζ T t h f.val
  have hf := ((sourceKPCompactGenuineL2Subspace_mem_ae K hζ (sourceKPArchHaar K hζ)
    f.val).mp f.prop) z
  have hcoe := sourceKPTranslateCompactPullbackL2_coe K hζ T t h f.val
  have hm := sourceKPTranslateCompactHaar_center_preserving K hζ T z
  have hshift := hm.quasiMeasurePreserving.ae_eq_comp hcoe
  have hχ := (sourceKPTranslateAutomorphicCompactMap_quasiMeasurePreserving K hζ T t h).ae_eq_comp hf
  change ∀ᵐ x ∂μJ, F (z • x) = f.val (p (z • x)) at hshift
  change ∀ᵐ x ∂μJ, f.val (z • p x) =
    (sourceKPAdelicCentralComplex K hζ z : ℂ) * f.val (p x) at hχ
  filter_upwards [hcoe, hshift, hχ] with x hFx hFzx hx
  have hp : p (z • x) = z • p x :=
    sourceKPTranslateAutomorphicCompactMap_center K hζ T t h z x
  change F x = f.val (p x) at hFx
  change F (z • x) = (sourceKPAdelicCentralComplex K hζ z : ℂ) * F x
  rw [hFzx, hp, hx, hFx]

end
end ArtinMatthews
