module

public import ArtinMatthews.SourceKPCuspPrincipalFrequency
public import ArtinMatthews.UnitTorusLocalRellich


set_option backward.privateInPublic true
@[expose] public section

/-! The original trace fundamental-domain Fourier average is exactly the
integral over the actual scaled Minkowski unit cell. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic Module.Free
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing MatrixGroups Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)

local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "Q" => SourceKPCuspPrincipalQuotient K d
local instance sourcePrincipalCellAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _
local instance sourcePrincipalCellAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance sourcePrincipalCellQuotientMeasurable : MeasurableSpace Q := borel _
local instance sourcePrincipalCellQuotientBorel : BorelSpace Q := ⟨rfl⟩

def sourceKPCuspUnitCellAdelicPoint (x : I → ℝ) : 𝔸[K] :=
  ArchimedeanCharacterLattice.Construction.mixedAdelicAdd K
    ((sourceKPCuspCoordinates K d hd).symm x)

theorem sourceKPCuspUnitCellAdelicPoint_torus (x : I → ℝ) :
    sourceKPCuspPrincipalTorusHomeomorph K d hd
      (QuotientAddGroup.mk (sourceKPCuspUnitCellAdelicPoint K d hd x)) =
      unitTorusUnitCellProjection I x := by
  let z := (sourceKPCuspCoordinates K d hd).symm x
  let e := sourceKPCuspArchQuotientHomeomorph K d hd
  have hz : e (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (sourceKPCuspUnitCellAdelicPoint K d hd x) :=
    sourceKPCuspArchQuotientEquiv_mk K d hd z
  rw [← hz]
  change sourceKPCuspTorusHomeomorph K d hd (e.symm (e (QuotientAddGroup.mk z))) = _
  rw [e.symm_apply_apply]
  change sourceKPCuspTorusEquiv K d hd (QuotientAddGroup.mk z) = _
  rw [sourceKPCuspTorusEquiv_mk]
  funext i
  rw [sourceKPCuspTorusHom_apply]
  change (((sourceKPCuspCoordinates K d hd) ((sourceKPCuspCoordinates K d hd).symm x) i : ℝ) : UnitAddCircle) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

include hζ in
theorem sourceKPCuspUnitCellAdelicPoint_measurePreserving :
    MeasurePreserving (fun x : I → ℝ => (QuotientAddGroup.mk (sourceKPCuspUnitCellAdelicPoint K d hd x) : Q))
      (unitTorusUnitCellMeasure I) (sourceKPCuspTraceHaar K d) := by
  have h := (sourceKPCuspPrincipalTorus_symm_measurePreserving K d hζ hd).comp
    (unitTorusUnitCellProjection_measurePreserving I)
  have he : (sourceKPCuspPrincipalTorusHomeomorph K d hd).symm ∘ unitTorusUnitCellProjection I =
      fun x => (QuotientAddGroup.mk (sourceKPCuspUnitCellAdelicPoint K d hd x) : Q) := by
    funext x
    change (sourceKPCuspPrincipalTorusHomeomorph K d hd).symm (unitTorusUnitCellProjection I x) = _
    rw [← sourceKPCuspUnitCellAdelicPoint_torus K d hd x,
      (sourceKPCuspPrincipalTorusHomeomorph K d hd).symm_apply_apply]
  rwa [he] at h

include hζ in
theorem sourceKPCuspPrincipalFrequency_integral_unitCell (m : K)
    (hm : ∃ r : 𝓞 K, m*(d:K) = (r:K)) (F : Q → ℂ) (hF : Measurable F) :
    (∫ a in sourceKPAdelicFundamentalDomain K,
        star (character K (algebraMap K 𝔸[K] m*a))*F (QuotientAddGroup.mk a)
        ∂sourceKPAdelicTraceProduct K) =
      ∫ x : I → ℝ, star (character K (algebraMap K 𝔸[K] m*sourceKPCuspUnitCellAdelicPoint K d hd x))*
        F (QuotientAddGroup.mk (sourceKPCuspUnitCellAdelicPoint K d hd x)) ∂unitTorusUnitCellMeasure I := by
  let G : Q → ℂ := fun x => star (sourceKPCuspPrincipalFrequency K d m hm x)*F x
  have hG : Measurable G := ((sourceKPCuspPrincipalFrequency_continuous K d m hm).star.measurable).mul hF
  have h₁ : (∫ x, G x ∂sourceKPCuspTraceHaar K d) =
      ∫ a in sourceKPAdelicFundamentalDomain K, G (QuotientAddGroup.mk a) ∂sourceKPAdelicTraceProduct K := by
    unfold sourceKPCuspTraceHaar
    exact integral_map QuotientAddGroup.continuous_mk.measurable.aemeasurable hG.aestronglyMeasurable
  have h := sourceKPCuspUnitCellAdelicPoint_measurePreserving K hζ d hd
  have hGm : AEStronglyMeasurable G (Measure.map
      (fun x : I → ℝ => (QuotientAddGroup.mk (sourceKPCuspUnitCellAdelicPoint K d hd x) : Q))
      (unitTorusUnitCellMeasure I)) := h.map_eq.symm ▸ hG.aestronglyMeasurable
  have h₂ := integral_map h.measurable.aemeasurable hGm
  rw [h.map_eq] at h₂
  exact h₁.symm.trans h₂

end
end ArtinMatthews
