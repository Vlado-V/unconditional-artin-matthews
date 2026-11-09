module

public import ArtinMatthews.SourceKPCompactGenuineH1
public import ArtinMatthews.SourceKPCubicCoreContraction


set_option backward.privateInPublic true
@[expose] public section

/-! The literal cubic core average extends to the actual compact quotient form. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter
open scoped NumberField MatrixGroups AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "T" => SourceKPCompactFormCore K hζ
local notation "V" => SourceKPCompactH1 K hζ
local notation "Vχ" => SourceKPCompactGenuineH1 K hζ
local notation "L" => SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ)
local notation "j" => sourceKPCompactH1Mass K hζ
local notation "e" => sourceKPCompactH1Core K hζ
local notation "Q" => sourceKPGenuineAutomorphicL2Projector K hζ
local notation "G" => sourceKPCompactGenuineL2Subspace K hζ (sourceKPArchHaar K hζ)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

def sourceKPCompactFormCoreProjector : T →L[ℂ] T := by
  let equiv := sourceKPCompactFormCoreLinearEquiv K hζ
  let p := equiv.symm.toLinearMap.comp
    ((sourceKPCubicCoreProjector K hζ 2).comp equiv.toLinearMap)
  refine p.mkContinuous 1 (fun f => ?_)
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg (p f)) (norm_nonneg f)]
  rw [sourceKPCompactFormCore_norm_sq K hζ (p f), sourceKPCompactFormCore_norm_sq K hζ f]
  exact sourceKPCubicCoreProjector_massEnergy_le K hζ f.val

theorem sourceKPCompactFormCoreProjector_val (f : T) :
    (sourceKPCompactFormCoreProjector K hζ f).val = sourceKPCubicCoreProjector K hζ 2 f.val :=
  rfl

theorem sourceKPCompactFormCoreProjector_mass (f : T) :
    sourceKPCompactFormCoreMassLinear K hζ (sourceKPCompactFormCoreProjector K hζ f) =
      Q (sourceKPCompactFormCoreMassLinear K hζ f) :=
  sourceKPCubicCoreMass_projector K hζ 2 f.val

theorem sourceKPCompactFormCoreProjector_genuine (f : T) (z : rootsOfUnity 3 K)
    (y : Y) :
    (sourceKPCompactFormCoreProjector K hζ f).val.val (z • y) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) *
        (sourceKPCompactFormCoreProjector K hζ f).val.val y := by
  let F := (sourceKPCompactFormCoreProjector K hζ f).val
  let g := sourceKPCompactCoreMass K hζ 2 F
  let : Measure.IsOpenPosMeasure μ := sourceKPAutomorphicCompactHaar_openPositive K hζ
  have hg : g ∈ G := sourceKPCubicCoreMass_projector_mem_genuine K hζ 2 f.val
  have he := ((sourceKPCompactGenuineL2Subspace_mem_ae K hζ (sourceKPArchHaar K hζ) g).mp hg) z
  have hF := sourceKPCompactCoreMass_coe K hζ F
  have hm := sourceKPAutomorphicCompactMeasure_center_preserving K hζ z (sourceKPArchHaar K hζ)
  have hshift := hm.quasiMeasurePreserving.ae_eq_comp hF
  have hAE : (fun x : Y => F.val (z • x)) =ᵐ[μ]
      (fun x : Y => (sourceKPAdelicCentralComplex K hζ z : ℂ) * F.val x) := by
    change ∀ᵐ x ∂μ, g (z • x) = F.val (z • x) at hshift
    filter_upwards [he, hF, hshift] with x hx hFx hshiftx
    exact hshiftx.symm.trans (hx.trans (congrArg _ hFx))
  have h := (Continuous.ae_eq_iff_eq μ
    (F.prop.1.comp (sourceKPCubicCenter_compact_continuous K hζ z))
    (continuous_const.mul F.prop.1)).mp hAE
  exact congrFun h y

def sourceKPCompactH1Projector : V →L[ℂ] V :=
  ((e).toContinuousLinearMap.comp (sourceKPCompactFormCoreProjector K hζ)).fromCompletion

local notation "P" => sourceKPCompactH1Projector K hζ

theorem sourceKPCompactH1Projector_core (f : T) :
    P (e f) = e (sourceKPCompactFormCoreProjector K hζ f) :=
  ((e).toContinuousLinearMap.comp (sourceKPCompactFormCoreProjector K hζ)).fromCompletion_apply_coe f

theorem sourceKPCompactH1Projector_mass (u : V) : j (P u) = Q (j u) := by
  refine (sourceKPCompactH1Core_denseRange K hζ).induction_on
    (p := fun v => j (P v) = Q (j v)) u
    (isClosed_eq ((j).continuous.comp (P).continuous) ((Q).continuous.comp (j).continuous)) ?_
  intro f
  rw [sourceKPCompactH1Projector_core, sourceKPCompactH1Mass_core, sourceKPCompactH1Mass_core]
  exact sourceKPCompactFormCoreProjector_mass K hζ f

theorem sourceKPCompactH1Projector_idempotent : IsIdempotentElem P := by
  change P * P = P
  ext u
  change P (P u) = P u
  refine (sourceKPCompactH1Core_denseRange K hζ).induction_on
    (p := fun v => P (P v) = P v) u
    (isClosed_eq ((P).continuous.comp (P).continuous) (P).continuous) ?_
  intro f
  rw [sourceKPCompactH1Projector_core, sourceKPCompactH1Projector_core]
  apply congrArg e
  apply sourceKPCompactFormCoreMassLinear_injective K hζ
  rw [sourceKPCompactFormCoreProjector_mass, sourceKPCompactFormCoreProjector_mass]
  exact congrArg (fun R : L →L[ℂ] L => R (sourceKPCompactFormCoreMassLinear K hζ f))
    (sourceKPCompactGenuineL2Projector_idempotent K hζ (sourceKPArchHaar K hζ)).eq

theorem sourceKPCompactH1Projector_mem_genuine (u : V) :
    P u ∈ sourceKPCompactGenuineH1 K hζ := by
  change j (P u) ∈ sourceKPCompactGenuineL2Subspace K hζ (sourceKPArchHaar K hζ)
  rw [sourceKPCompactH1Projector_mass, ← sourceKPCompactGenuineL2Projector_range]
  exact ⟨j u, rfl⟩

def sourceKPCompactH1ProjectToGenuine : V →L[ℂ] Vχ :=
  (P).codRestrict (sourceKPCompactGenuineH1 K hζ) (sourceKPCompactH1Projector_mem_genuine K hζ)

def sourceKPCompactGenuineH1ProjectedCore : T →L[ℂ] Vχ :=
  (sourceKPCompactH1ProjectToGenuine K hζ).comp (e).toContinuousLinearMap

theorem sourceKPCompactGenuineH1ProjectedCore_val (f : T) :
    (sourceKPCompactGenuineH1ProjectedCore K hζ f).val =
      e (sourceKPCompactFormCoreProjector K hζ f) :=
  sourceKPCompactH1Projector_core K hζ f

theorem sourceKPCompactH1ProjectToGenuine_surjective (hinj : Function.Injective j) :
    Function.Surjective (sourceKPCompactH1ProjectToGenuine K hζ) := by
  intro u
  refine ⟨u.val, Subtype.ext ?_⟩
  change P u.val = u.val
  apply hinj
  rw [sourceKPCompactH1Projector_mass]
  exact (sourceKPCompactGenuineL2Projector_fixed_iff K hζ (sourceKPArchHaar K hζ) _).mpr u.prop

theorem sourceKPCompactGenuineH1ProjectedCore_denseRange (hinj : Function.Injective j) :
    DenseRange (sourceKPCompactGenuineH1ProjectedCore K hζ) :=
  (sourceKPCompactH1ProjectToGenuine_surjective K hζ hinj).denseRange.comp
    (sourceKPCompactH1Core_denseRange K hζ) (sourceKPCompactH1ProjectToGenuine K hζ).continuous

theorem sourceKPCompactGenuineH1Mass_injective_of (hinj : Function.Injective j) :
    Function.Injective (sourceKPCompactGenuineH1Mass K hζ) := by
  intro u v huv
  apply Subtype.ext
  apply hinj
  exact congrArg (fun g : SourceKPGenuineAutomorphicL2 K hζ => (g : L)) huv

theorem sourceKPCompactGenuineH1Mass_denseRange_of (hdense : DenseRange j) :
    DenseRange (sourceKPCompactGenuineH1Mass K hζ) := by
  let qg : L →L[ℂ] SourceKPGenuineAutomorphicL2 K hζ :=
    (Q).codRestrict G (fun f => by
      rw [← sourceKPCompactGenuineL2Projector_range]
      exact ⟨f, rfl⟩)
  have hqg : Function.Surjective qg := by
    intro g
    refine ⟨g.val, Subtype.ext ?_⟩
    exact (sourceKPCompactGenuineL2Projector_fixed_iff K hζ (sourceKPArchHaar K hζ) g.val).mpr g.prop
  refine (hqg.denseRange.comp hdense qg.continuous).mono ?_
  rintro _ ⟨u, rfl⟩
  refine ⟨sourceKPCompactH1ProjectToGenuine K hζ u, Subtype.ext ?_⟩
  exact sourceKPCompactH1Projector_mass K hζ u

end
end ArtinMatthews
