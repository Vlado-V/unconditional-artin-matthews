module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.RealOperators
public import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier


set_option backward.privateInPublic true
@[expose] public section

/-! # Real Faithful -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.RealFaithful.CM

noncomputable section

/-! The real extension is faithful, detected on tensors with the actual
integral finite vacuum. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.FiniteOperators.CM.Sections
variable {I : Type*} [Fintype I]

theorem operator_injective : Function.Injective (RealOperators.CM.operator (I := I)) := by
  intro U V he
  apply LinearEquiv.ext
  intro f
  apply Subtype.ext
  funext x
  have h := congrArg (fun W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I =>
    (W (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction)).val (FiniteOperators.CM.Sections.join x 0)) he
  rw [RealOperators.CM.operator_tensor, RealOperators.CM.operator_tensor] at h
  change (U f).val x * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator (0 : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) = (V f).val x * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator (0 : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) at h
  rwa [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem, mul_one, mul_one] at h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.RealFaithful.CM
