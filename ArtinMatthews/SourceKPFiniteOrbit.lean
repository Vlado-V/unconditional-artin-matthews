module

public import ArtinMatthews.SourceKPArchComponent


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def SourceKPFiniteOrbit :=
  Quotient (MulAction.orbitRel (PGL(2, K)) (SourceKPFiniteLevelFiber K hζ))

instance sourceKPFiniteOrbit_topology : TopologicalSpace (SourceKPFiniteOrbit K hζ) := ⊥
instance sourceKPFiniteOrbit_discrete : DiscreteTopology (SourceKPFiniteOrbit K hζ) := ⟨rfl⟩

def sourceKPFiniteOrbitMk (b : SourceKPFiniteLevelFiber K hζ) : SourceKPFiniteOrbit K hζ :=
  Quotient.mk _ b

def sourceKPAutomorphicFiniteOrbit : SourceKPAutomorphicLevel K hζ → SourceKPFiniteOrbit K hζ :=
  Quotient.lift (fun x : SourceKPFiniteLevelSpace K hζ => sourceKPFiniteOrbitMk K hζ x.2) (by
    intro x y hxy
    obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp hxy
    apply Quotient.sound
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨γ,congrArg (fun x : SourceKPFiniteLevelSpace K hζ => x.2) hγ⟩)

theorem sourceKPAutomorphicFiniteOrbit_component (b : SourceKPFiniteLevelFiber K hζ)
    (a : PGL(2, InfiniteAdeleRing K)) :
    sourceKPAutomorphicFiniteOrbit K hζ (sourceKPArchComponentPoint K hζ b a) =
      sourceKPFiniteOrbitMk K hζ b := rfl

theorem sourceKPAutomorphicFiniteOrbit_continuous : Continuous (sourceKPAutomorphicFiniteOrbit K hζ) :=
  ((continuous_of_discreteTopology : Continuous (sourceKPFiniteOrbitMk K hζ)).comp
    continuous_snd).quotient_lift _

theorem sourceKPArchComponentPoint_continuous (b : SourceKPFiniteLevelFiber K hζ) :
    Continuous (sourceKPArchComponentPoint K hζ b) :=
  continuous_quot_mk.comp (continuous_id.prodMk continuous_const)

theorem sourceKPArchComponentEmbedding_continuous (b : SourceKPFiniteLevelFiber K hζ) :
    Continuous (sourceKPArchComponentEmbedding K hζ b) :=
  (sourceKPArchComponentPoint_continuous K hζ b).quotient_lift _

theorem sourceKPArchComponent_range (b : SourceKPFiniteLevelFiber K hζ) :
    Set.range (sourceKPArchComponentPoint K hζ b) =
      (sourceKPAutomorphicFiniteOrbit K hζ) ⁻¹' {sourceKPFiniteOrbitMk K hζ b} := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    rfl
  · intro hx
    induction x using Quotient.inductionOn with
    | _ x =>
      obtain ⟨a,c⟩ := x
      change sourceKPFiniteOrbitMk K hζ c = sourceKPFiniteOrbitMk K hζ b at hx
      obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hx)
      refine ⟨(sourceKPRationalArchMap K hζ γ)⁻¹ * a,?_⟩
      apply Eq.symm
      apply Quotient.sound
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨γ,Prod.ext ?_ hγ⟩
      change sourceKPRationalArchMap K hζ γ * ((sourceKPRationalArchMap K hζ γ)⁻¹ * a) = a
      exact mul_inv_cancel_left _ _

theorem sourceKPArchComponent_range_clopen (b : SourceKPFiniteLevelFiber K hζ) :
    IsClopen (Set.range (sourceKPArchComponentPoint K hζ b)) := by
  rw [sourceKPArchComponent_range]
  exact (isClopen_discrete _).preimage (sourceKPAutomorphicFiniteOrbit_continuous K hζ)

end
end ArtinMatthews
