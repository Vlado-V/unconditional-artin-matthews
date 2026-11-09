module

public import ArtinMatthews.SourceKPFiniteChartL2Lift


set_option backward.privateInPublic true
@[expose] public section

/-! The exact rational relation between upper-coordinate representatives of the true cover quotient. -/
namespace ArtinMatthews
open NumberField Matrix MulOpposite
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCompactUpperRepresentative_exists (p : SourceKPArchUpperHalfSpace K) :
    ∃ a : PGL(2, InfiniteAdeleRing K),
      sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a) = p := by
  obtain ⟨a,ha⟩ := QuotientGroup.mk_surjective ((sourceKPArchSymmetricHomeomorph K hζ).symm p)
  refine ⟨a,?_⟩
  rw [ha,Homeomorph.apply_symm_apply]

theorem sourceKPUpperToCompact_mk (b : SourceKPFiniteLevelFiber K hζ)
    (a : PGL(2, InfiniteAdeleRing K)) :
    sourceKPUpperToCompact K hζ b (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a)) =
      sourceKPAutomorphicCompactMk K hζ (sourceKPArchComponentPoint K hζ b a) :=
  sourceKPArithmeticUpperComponentHomeomorph_mk K hζ b a

theorem sourceKPUpperToCompact_rational (γ : PGL(2, K)) (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) :
    sourceKPUpperToCompact K hζ (γ • b)
      (sourceKPArchUpperAction K hζ (sourceKPRationalArchMap K hζ γ) p) =
        sourceKPUpperToCompact K hζ b p := by
  obtain ⟨a,rfl⟩ := sourceKPCompactUpperRepresentative_exists K hζ p
  rw [← sourceKPArchSymmetricHomeomorph_smul]
  change sourceKPUpperToCompact K hζ (γ • b)
      (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk (sourceKPRationalArchMap K hζ γ * a))) = _
  rw [sourceKPUpperToCompact_mk,sourceKPUpperToCompact_mk]
  apply congrArg (sourceKPAutomorphicCompactMk K hζ)
  apply Quotient.sound
  exact MulAction.mem_orbit_iff.mpr ⟨γ,rfl⟩

theorem sourceKPUpperToCompact_eq_iff_rational (b c : SourceKPFiniteLevelFiber K hζ)
    (p q : SourceKPArchUpperHalfSpace K) :
    sourceKPUpperToCompact K hζ b p = sourceKPUpperToCompact K hζ c q ↔
      ∃ γ : PGL(2, K), γ • c = b ∧
        sourceKPArchUpperAction K hζ (sourceKPRationalArchMap K hζ γ) q = p := by
  constructor
  · intro h
    obtain ⟨a,ha⟩ := sourceKPCompactUpperRepresentative_exists K hζ p
    obtain ⟨d,hd⟩ := sourceKPCompactUpperRepresentative_exists K hζ q
    rw [← ha,← hd,sourceKPUpperToCompact_mk,sourceKPUpperToCompact_mk] at h
    obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h)
    have hk' : sourceKPArchComponentPoint K hζ c (d * unop k.val) =
        sourceKPArchComponentPoint K hζ b a := hk
    obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hk'.symm)
    have hfin : γ • c = b := congrArg Prod.snd hγ
    have harch : sourceKPRationalArchMap K hζ γ * (d * unop k.val) = a := congrArg Prod.fst hγ
    refine ⟨γ,hfin,?_⟩
    rw [← ha,← hd,← sourceKPArchSymmetricHomeomorph_smul]
    change sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk (sourceKPRationalArchMap K hζ γ * d)) =
      sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a)
    apply congrArg (sourceKPArchSymmetricHomeomorph K hζ)
    have hmem : unop k.val ∈ sourceKPArchBaseCompactSubgroup K hζ := k.prop
    rw [← harch,← mul_assoc,QuotientGroup.mk_mul_of_mem _ hmem]
  · rintro ⟨γ,hfin,harch⟩
    simpa only [hfin,harch] using sourceKPUpperToCompact_rational K hζ γ c q

end
end ArtinMatthews
