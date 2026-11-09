module

public import ArtinMatthews.SourceKPFiniteLevelTopology


set_option backward.privateInPublic true
@[expose] public section

/-! The actual rational stabilizer of a finite coset and its archimedean
image. These are the subgroups required for the arithmetic component
geometry; no discreteness or finite-covolume conclusion is assumed. -/

namespace ArtinMatthews
open NumberField Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPRationalArchMap : PGL(2, K) →* PGL(2, InfiniteAdeleRing K) :=
  (MonoidHom.fst _ _).comp (sourceKPAdelicProjectiveRationalLift K hζ)

def sourceKPRationalFiniteMap : PGL(2, K) →* SourceKPFiniteAdeleProjective K hζ :=
  (MonoidHom.snd _ _).comp (sourceKPAdelicProjectiveRationalLift K hζ)

instance sourceKPRationalFiniteFiberAction : MulAction (PGL(2, K)) (SourceKPFiniteLevelFiber K hζ) :=
  MulAction.compHom _ (sourceKPRationalFiniteMap K hζ)

def sourceKPRationalFiniteStabilizer (b : SourceKPFiniteLevelFiber K hζ) : Subgroup (PGL(2, K)) :=
  MulAction.stabilizer (PGL(2, K)) b

def sourceKPArchComponentSubgroup (b : SourceKPFiniteLevelFiber K hζ) :
    Subgroup (PGL(2, InfiniteAdeleRing K)) :=
  (sourceKPRationalFiniteStabilizer K hζ b).map (sourceKPRationalArchMap K hζ)

def sourceKPArchComponentPoint (b : SourceKPFiniteLevelFiber K hζ)
    (a : PGL(2, InfiniteAdeleRing K)) : SourceKPAutomorphicLevel K hζ := Quotient.mk _ (a,b)

theorem sourceKPArchComponentPoint_eq_iff (b : SourceKPFiniteLevelFiber K hζ)
    (a c : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchComponentPoint K hζ b a = sourceKPArchComponentPoint K hζ b c ↔
      ∃ γ ∈ sourceKPRationalFiniteStabilizer K hζ b, sourceKPRationalArchMap K hζ γ * c = a := by
  constructor
  · intro h
    obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h)
    refine ⟨γ,?_,?_⟩
    · exact congrArg (fun x : SourceKPFiniteLevelSpace K hζ => x.2) hγ
    · exact congrArg (fun x : SourceKPFiniteLevelSpace K hζ => x.1) hγ
  · rintro ⟨γ,hγ,ha⟩
    apply Quotient.sound
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨γ,Prod.ext ha hγ⟩

theorem sourceKPArchComponentPoint_eq_iff_rel (b : SourceKPFiniteLevelFiber K hζ)
    (a c : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchComponentPoint K hζ b a = sourceKPArchComponentPoint K hζ b c ↔
      QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ b) a c := by
  rw [sourceKPArchComponentPoint_eq_iff, QuotientGroup.rightRel_apply]
  constructor
  · rintro ⟨γ,hγ,hac⟩
    refine ⟨γ⁻¹,(sourceKPRationalFiniteStabilizer K hζ b).inv_mem hγ,?_⟩
    rw [map_inv, ← hac]
    simp only [_root_.mul_inv_rev, mul_inv_cancel_left]
  · rintro ⟨γ,hγ,hgc⟩
    refine ⟨γ⁻¹,(sourceKPRationalFiniteStabilizer K hζ b).inv_mem hγ,?_⟩
    rw [map_inv,hgc]
    simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]

def sourceKPArchComponentEmbedding (b : SourceKPFiniteLevelFiber K hζ) :
    Quotient (QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ b)) ↪
      SourceKPAutomorphicLevel K hζ where
  toFun := Quotient.lift (sourceKPArchComponentPoint K hζ b)
    (fun a c h => (sourceKPArchComponentPoint_eq_iff_rel K hζ b a c).mpr h)
  inj' := by
    intro x y
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ c =>
        intro h
        exact Quotient.sound ((sourceKPArchComponentPoint_eq_iff_rel K hζ b a c).mp h)

theorem sourceKPArchComponentEmbedding_mk (b : SourceKPFiniteLevelFiber K hζ)
    (a : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchComponentEmbedding K hζ b (Quotient.mk _ a) = sourceKPArchComponentPoint K hζ b a := rfl

end
end ArtinMatthews
