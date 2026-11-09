module

public import ArtinMatthews.SourceCubicTorusExtension


set_option backward.privateInPublic true
@[expose] public section

/-! Pull back the proved cubic extension to the literal F_S unit group.
This is an actual central extension, rather than merely an extension of
its finite power-class quotient. Allowed global generators have a
derived multiplicative lift through the same chosen B6. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

def sourceCubicUnitClassMap : (SLocalRing K S)ˣ →* SourceCubicTorusBase K S :=
  QuotientGroup.mk' (powMonoidHom (6 : ℕ) : (SLocalRing K S)ˣ →* (SLocalRing K S)ˣ).range

def sourceCubicUnitTorusSubgroup : Subgroup (SourceCubicTorus K hζ S × (SLocalRing K S)ˣ) where
  carrier := {p | sourceCubicTorusProjection K hζ S p.1 = sourceCubicUnitClassMap K S p.2}
  one_mem' := rfl
  mul_mem' {p q} hp hq := by
    change sourceCubicTorusProjection K hζ S (p.1 * q.1) = sourceCubicUnitClassMap K S (p.2 * q.2)
    rw [map_mul, map_mul, hp, hq]
  inv_mem' {p} hp := by
    change sourceCubicTorusProjection K hζ S p.1⁻¹ = sourceCubicUnitClassMap K S p.2⁻¹
    rw [map_inv, map_inv, hp]

abbrev SourceCubicLocalUnitTorus := sourceCubicUnitTorusSubgroup K hζ S

def sourceCubicLocalUnitProjection : SourceCubicLocalUnitTorus K hζ S →* (SLocalRing K S)ˣ :=
  (MonoidHom.snd (SourceCubicTorus K hζ S) (SLocalRing K S)ˣ).comp
    (sourceCubicUnitTorusSubgroup K hζ S).subtype

theorem sourceCubicLocalUnitProjection_surjective :
    Function.Surjective (sourceCubicLocalUnitProjection K hζ S) := by
  intro u
  exact ⟨⟨(⟨1, sourceCubicUnitClassMap K S u⟩, u), rfl⟩, rfl⟩

def sourceCubicLocalUnitCenter : rootsOfUnity 3 K →* SourceCubicLocalUnitTorus K hζ S where
  toFun z := ⟨(sourceCubicTorusCenter K hζ S z, 1), rfl⟩
  map_one' := rfl
  map_mul' z w := by
    apply Subtype.ext
    apply Prod.ext
    · exact (sourceCubicTorusCenter K hζ S).map_mul z w
    · exact (one_mul (1 : (SLocalRing K S)ˣ)).symm

theorem sourceCubicLocalUnitCenter_injective :
    Function.Injective (sourceCubicLocalUnitCenter K hζ S) := by
  intro z w h
  exact (sourceCubicTorusCenter_injective K hζ S)
    (congrArg (fun x : SourceCubicLocalUnitTorus K hζ S => x.val.1) h)

theorem sourceCubicLocalUnit_exact :
    (sourceCubicLocalUnitCenter K hζ S).range = (sourceCubicLocalUnitProjection K hζ S).ker := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    rfl
  · intro hp
    change p.val.2 = 1 at hp
    refine ⟨p.val.1.central, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · apply SourceCubicTorus.ext
      · rfl
      · have hb := p.property
        change p.val.1.base = sourceCubicUnitClassMap K S p.val.2 at hb
        rw [hp, map_one] at hb
        exact hb.symm
    · exact hp.symm

theorem sourceCubicLocalUnitCenter_commute (z : rootsOfUnity 3 K)
    (p : SourceCubicLocalUnitTorus K hζ S) :
    Commute (sourceCubicLocalUnitCenter K hζ S z) p := by
  apply Subtype.ext
  apply Prod.ext
  · exact sourceCubicTorusCenter_commute K hζ S z p.val.1
  · exact (one_mul p.val.2).trans (mul_one p.val.2).symm

def sourceAllowedCubicTorusLift (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    allowedSubgroup K hζ S₀ →* SourceCubicLocalUnitTorus K hζ (sourceHilbertSet K S₀) where
  toFun a :=
    ⟨(sourceCubicTorusChosenSection K hζ S₀
        ⟨sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) a.val, a.property⟩,
      Units.map (sLocalRingDiagonal K (sourceHilbertSet K S₀)).toMonoidHom a.val), rfl⟩
  map_one' := rfl
  map_mul' a b := by
    apply Subtype.ext
    apply Prod.ext
    · apply SourceCubicTorus.ext
      · change 1 = 1 * 1 * sourceCubicTorusPair K hζ (sourceHilbertSet K S₀)
          (sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) a.val)
          (sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) b.val)
        change 1 = 1 * 1 * sourceSexticRootSquare K
          (paperSourceHilbertForm K hζ (sourceHilbertSet K S₀)
            (sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) a.val)
            (sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) b.val))
        rw [chosenB_isotropic K hζ S₀ _ a.property _ b.property, map_one]
        simp
      · exact (sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀)).map_mul a.val b.val
    · exact (Units.map (sLocalRingDiagonal K (sourceHilbertSet K S₀)).toMonoidHom).map_mul a.val b.val

theorem sourceAllowedCubicTorusLift_projection (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (a : allowedSubgroup K hζ S₀) :
    sourceCubicLocalUnitProjection K hζ (sourceHilbertSet K S₀) (sourceAllowedCubicTorusLift K hζ S₀ a) =
      Units.map (sLocalRingDiagonal K (sourceHilbertSet K S₀)).toMonoidHom a.val := rfl

end
end ArtinMatthews
