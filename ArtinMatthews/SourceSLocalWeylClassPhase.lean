module

public import ArtinMatthews.SourceSLocalFiniteWeyl


set_option backward.privateInPublic true
@[expose] public section

/-! The retained Weyl phase descends to the genuine S-local cube
classes via the existing finite-place Hilbert pairings. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain ClassFieldTheory GlobalClassFieldTheory.Reciprocity
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Q" => SWholePowerClasses K 3 S

private abbrev sourceSLocalWeylCubeClass : SWholeUnits K S →* Q :=
  QuotientGroup.mk' (powMonoidHom (3 : ℕ) : SWholeUnits K S →* SWholeUnits K S).range

local notation "q" => sourceSLocalWeylCubeClass K S

def sourceSLocalWeylClassPhase (a x : Q) : rootsOfUnity 3 K := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  exact ∏ P : S, (sourceKPRootsTransport K hζ P.val).symm
    (finitePlaceAdicHilbertPairingFamily K 3
      (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)) P.val
      (sWholePowerEquiv K 3 S a P) (sWholePowerEquiv K 3 S x P)⁻¹ ^ 2)

theorem sourceSLocalWeylPhase_eq_classPhase (b : Kˣ) (x : SWholeUnits K S) :
    sourceSLocalWeylPhase K S hζ b x =
      sourceSLocalWeylClassPhase K S hζ (sWholeGlobalClassMap K 3 S ((b⁻¹)^2)) (q x) := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  rw [sourceSLocalWeylPhase_eq_hilbert_product]
  simp only [sourceSLocalWeylClassPhase,sourceSLocalWeylCubeClass,
    sWholePowerEquiv_globalClass]
  apply Finset.prod_congr rfl
  intro P _
  change _ = (sourceKPRootsTransport K hζ P.val).symm
    (finitePlaceAdicHilbertPairingFamily K 3
      (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)) P.val
      (powerClass (P.val.adicCompletion K) 3 ((sWholeDiagonal K S ((b⁻¹)^2)).2 P))
      (powerClass (P.val.adicCompletion K) 3 (x.2 P))⁻¹ ^ 2)
  rw [← map_inv (powerClass (P.val.adicCompletion K) 3)] <;> rfl

theorem sourceSLocalWeylPhase_mul_cube (b : Kˣ) (x u : SWholeUnits K S) :
    sourceSLocalWeylPhase K S hζ b (x*u^3) = sourceSLocalWeylPhase K S hζ b x := by
  have hu : q (u^3) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨u,rfl⟩
  rw [sourceSLocalWeylPhase_eq_classPhase,sourceSLocalWeylPhase_eq_classPhase,map_mul,hu]
  exact congrArg (sourceSLocalWeylClassPhase K S hζ (sWholeGlobalClassMap K 3 S ((b⁻¹)^2)))
    (mul_one (q x))

end
end ArtinMatthews
