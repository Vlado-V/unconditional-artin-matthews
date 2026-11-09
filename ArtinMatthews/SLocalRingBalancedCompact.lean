module

public import ArtinMatthews.AllowedBalancedGenerator


set_option backward.privateInPublic true
@[expose] public section

/-! The compact balancing set and source scaling on the literal
product ring F_S, identified topologically with the product of local
multiplicative groups. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SUnitGroup
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def sLocalRingUnitsTopologicalEquiv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (SLocalRing K S)ˣ ≃ₜ* SWholeUnits K S where
  __ := sLocalRingUnitsEquiv K S
  continuous_toFun :=
    ((Homeomorph.prodCongr ContinuousMulEquiv.piUnits.toHomeomorph
      ContinuousMulEquiv.piUnits.toHomeomorph).continuous.comp Homeomorph.prodUnits.continuous)
  continuous_invFun :=
    (Homeomorph.prodUnits.symm.continuous.comp
      (Homeomorph.prodCongr ContinuousMulEquiv.piUnits.toHomeomorph
        ContinuousMulEquiv.piUnits.toHomeomorph).symm.continuous)

@[simp] theorem sLocalRingUnitsTopologicalEquiv_diagonal
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    sLocalRingUnitsTopologicalEquiv K S
      (Units.map (sLocalRingDiagonal K S).toMonoidHom a) = sWholeDiagonal K S a := rfl

def sLocalRingNorm (S : Finset (HeightOneSpectrum (𝓞 K))) (a : (SLocalRing K S)ˣ) : ℝ :=
  sLocalNorm K S (sLocalRingUnitsTopologicalEquiv K S a)

def sourceBalancedCompactSet (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (SLocalRing K S)ˣ :=
  (sLocalRingUnitsTopologicalEquiv K S).symm '' sixthBalancedCompactSet K S

theorem sourceBalancedCompactSet_isCompact (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsCompact (sourceBalancedCompactSet K S) :=
  (sixthBalancedCompactSet_isCompact K S).image (sLocalRingUnitsTopologicalEquiv K S).symm.continuous

theorem sourceBalancedCompactSet_norm (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a : (SLocalRing K S)ˣ} (ha : a ∈ sourceBalancedCompactSet K S) : sLocalRingNorm K S a = 1 := by
  obtain ⟨y, hy, rfl⟩ := ha
  unfold sLocalRingNorm
  rw [(sLocalRingUnitsTopologicalEquiv K S).apply_symm_apply]
  exact sixthBalancedCompactSet_norm K S hy

def sourceRingScaling {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : ℝ) : (SLocalRing K S)ˣ :=
  (sLocalRingUnitsTopologicalEquiv K S).symm (sLocalPositiveScaling K hζ S T)

theorem sourceRingScaling_norm {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {T : ℝ} (hT : 0 < T) :
    sLocalRingNorm K S (sourceRingScaling K hζ S T) = T := by
  unfold sourceRingScaling sLocalRingNorm
  rw [(sLocalRingUnitsTopologicalEquiv K S).apply_symm_apply]
  exact sLocalPositiveScaling_norm K hζ S hT

namespace AllowedGenerators

theorem balancedGenerator_sourceRing_compact {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) :
    Units.map (sLocalRingDiagonal K (sourceHilbertSet K S₀)).toMonoidHom
        (balancedGenerator K hζ S₀ I) /
      sourceRingScaling K hζ (sourceHilbertSet K S₀) (idealSNorm K hζ S₀ I) ∈
        sourceBalancedCompactSet K (sourceHilbertSet K S₀) := by
  let S := sourceHilbertSet K S₀
  let e := sLocalRingUnitsTopologicalEquiv K S
  let x := Units.map (sLocalRingDiagonal K S).toMonoidHom (balancedGenerator K hζ S₀ I) /
    sourceRingScaling K hζ S (idealSNorm K hζ S₀ I)
  refine ⟨e x, ?_, e.symm_apply_apply x⟩
  change e x ∈ sixthBalancedCompactSet K S
  dsimp only [x]
  rw [map_div, sLocalRingUnitsTopologicalEquiv_diagonal]
  change sWholeDiagonal K S (balancedGenerator K hζ S₀ I) /
    e (e.symm (sLocalPositiveScaling K hζ S (idealSNorm K hζ S₀ I))) ∈ _
  rw [e.apply_symm_apply]
  exact balancedGenerator_compact K hζ S₀ I

end AllowedGenerators
end
end ArtinMatthews
