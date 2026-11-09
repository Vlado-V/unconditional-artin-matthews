module

public import ArtinMatthews.SourceKPCubicCenterAction


set_option backward.privateInPublic true
@[expose] public section

/-! The cubic center preserves each archimedean stabilizer and transports
the actual component embeddings through the identity archimedean map. -/

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCubicCenter_rationalStabilizer (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ) :
    sourceKPRationalFiniteStabilizer K hζ (z • b) = sourceKPRationalFiniteStabilizer K hζ b :=
  MulAction.stabilizer_smul_eq_right (G := PGL(2, K)) z b

theorem sourceKPCubicCenter_archSubgroup (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ) :
    sourceKPArchComponentSubgroup K hζ (z • b) = sourceKPArchComponentSubgroup K hζ b := by
  simp only [sourceKPArchComponentSubgroup, sourceKPCubicCenter_rationalStabilizer]

theorem sourceKPCubicCenter_component_point (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ) (a : PGL(2, InfiniteAdeleRing K)) :
    z • sourceKPArchComponentPoint K hζ b a = sourceKPArchComponentPoint K hζ (z • b) a := by
  change (Quotient.mk _ (z • (a, b)) : SourceKPAutomorphicLevel K hζ) = Quotient.mk _ (a, z • b)
  rw [sourceKPCubicCenter_finiteLevel_pair]

def sourceKPCubicCenterComponentHomeomorph (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ) :
    Quotient (QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ b)) ≃ₜ
      Quotient (QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ (z • b))) where
  toEquiv := Quotient.congr (Equiv.refl _) (by
    intro a c
    rw [sourceKPCubicCenter_archSubgroup]
    rfl)
  continuous_toFun := continuous_quot_mk.quotient_lift _
  continuous_invFun := continuous_quot_mk.quotient_lift _

theorem sourceKPCubicCenterComponentHomeomorph_mk (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ) (a : PGL(2, InfiniteAdeleRing K)) :
    sourceKPCubicCenterComponentHomeomorph K hζ z b (Quotient.mk _ a) = Quotient.mk _ a := rfl

theorem sourceKPCubicCenter_component_embedding (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ)
    (x : Quotient (QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ b))) :
    z • sourceKPArchComponentEmbedding K hζ b x =
      sourceKPArchComponentEmbedding K hζ (z • b) (sourceKPCubicCenterComponentHomeomorph K hζ z b x) := by
  induction x using Quotient.inductionOn with
  | _ a => exact sourceKPCubicCenter_component_point K hζ z b a

theorem sourceKPCubicCenter_inverse_eval
    (F : SourceKPAutomorphicLevel K hζ → ℂ)
    (hF : ∀ (z : rootsOfUnity 3 K) (x : SourceKPAutomorphicLevel K hζ),
      F (z • x) = (sourceKPAdelicCentralComplex K hζ z : ℂ) * F x)
    (z : rootsOfUnity 3 K) (x : SourceKPAutomorphicLevel K hζ) :
    F (z⁻¹ • x) = (sourceKPAdelicCentralComplex K hζ z : ℂ)⁻¹ * F x := by
  simpa only [map_inv, Units.val_inv_eq_inv_val] using hF z⁻¹ x

end
end ArtinMatthews
