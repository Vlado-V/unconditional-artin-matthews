module

public import ArtinMatthews.SLocalWholeSourceComplement
public import Mathlib.Algebra.Group.Pi.Units


set_option backward.privateInPublic true
@[expose] public section

/-! Source-faithful ring presentation: F_S is the actual product of
all infinite completions and the finite completions in S. Its group
of units modulo sixth powers has the constructed isotropic complement
to the literal diagonal S-unit image. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain KummerTheory
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

abbrev SLocalRing (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (∀ w : InfinitePlace K, w.Completion) × (∀ v : S, v.1.adicCompletion K)

abbrev SLocalRingPowerClasses (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (SLocalRing K S)ˣ ⧸ (powMonoidHom (n : ℕ) : (SLocalRing K S)ˣ →* (SLocalRing K S)ˣ).range

def sLocalRingDiagonal (S : Finset (HeightOneSpectrum (𝓞 K))) : K →+* SLocalRing K S :=
  (RingHom.pi fun w : InfinitePlace K => algebraMap K w.Completion).prod
    (RingHom.pi fun v : S => algebraMap K (v.1.adicCompletion K))

def sLocalRingGlobalClassMap (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Kˣ →* SLocalRingPowerClasses K n S :=
  (QuotientGroup.mk' _).comp (Units.map (sLocalRingDiagonal K S).toMonoidHom)

def sLocalRingUnitImage (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (SLocalRingPowerClasses K n S) :=
  ((sLocalRingGlobalClassMap K n S).comp (SUnitGroup (K := K) S).subtype).range

def sLocalRingUnitsEquiv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (SLocalRing K S)ˣ ≃* SWholeUnits K S :=
  MulEquiv.prodUnits.trans (MulEquiv.prodCongr MulEquiv.piUnits MulEquiv.piUnits)

def sLocalRingPowerEquiv (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SLocalRingPowerClasses K n S ≃* SWholePowerClasses K n S :=
  LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv _ _ (n : ℕ) (sLocalRingUnitsEquiv K S)

@[simp] theorem sLocalRingPowerEquiv_globalClass (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    sLocalRingPowerEquiv K n S (sLocalRingGlobalClassMap K n S a) = sWholeGlobalClassMap K n S a := rfl

theorem sLocalRingPowerEquiv_unitImage_iff (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : SLocalRingPowerClasses K n S) :
    x ∈ sLocalRingUnitImage K n S ↔ sLocalRingPowerEquiv K n S x ∈ sWholeUnitPowerImage K n S := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, hu⟩
    refine ⟨u, (sLocalRingPowerEquiv K n S).injective ?_⟩
    change sLocalRingPowerEquiv K n S (sLocalRingGlobalClassMap K n S (u : Kˣ)) = _
    rw [sLocalRingPowerEquiv_globalClass]
    exact hu

def sourceRingHilbertForm {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SLocalRingPowerClasses K 6 S →* (SLocalRingPowerClasses K 6 S →* rootsOfUnity 6 K) :=
  ((MonoidHom.compHom' (M := SLocalRingPowerClasses K 6 S) (N := SWholePowerClasses K 6 S)
      (P := rootsOfUnity 6 K)) (sLocalRingPowerEquiv K 6 S).toMonoidHom).comp
    ((sourceWholeHilbertForm K hζ S).comp (sLocalRingPowerEquiv K 6 S).toMonoidHom)

@[simp] theorem sourceRingHilbertForm_apply {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x y : SLocalRingPowerClasses K 6 S) :
    sourceRingHilbertForm K hζ S x y = sourceWholeHilbertForm K hζ S
      (sLocalRingPowerEquiv K 6 S x) (sLocalRingPowerEquiv K 6 S y) := rfl

theorem source_ring_sixth_isotropic_complement {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ B : Subgroup (SLocalRingPowerClasses K 6 (sourceHilbertSet K S₀)),
      IsCompl (sLocalRingUnitImage K 6 (sourceHilbertSet K S₀)) B ∧
      ∀ x ∈ B, ∀ y ∈ B, sourceRingHilbertForm K hζ (sourceHilbertSet K S₀) x y = 1 := by
  obtain ⟨B, hC, hI⟩ := source_sixth_whole_isotropic_complement K hζ S₀
  let e := sLocalRingPowerEquiv K 6 (sourceHilbertSet K S₀)
  have he : (sWholeUnitPowerImage K 6 (sourceHilbertSet K S₀)).comap e.toMonoidHom =
      sLocalRingUnitImage K 6 (sourceHilbertSet K S₀) := by
    ext x
    exact (sLocalRingPowerEquiv_unitImage_iff K 6 (sourceHilbertSet K S₀) x).symm
  have h := e.comapSubgroup.isCompl hC
  change IsCompl ((sWholeUnitPowerImage K 6 (sourceHilbertSet K S₀)).comap e.toMonoidHom)
    (B.comap e.toMonoidHom) at h
  rw [he] at h
  refine ⟨B.comap e.toMonoidHom, h, ?_⟩
  intro x hx y hy
  exact hI (e x) hx (e y) hy

theorem source_ring_sixth_unitImage_selfOrthogonal {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ x : SLocalRingPowerClasses K 6 (sourceHilbertSet K S₀),
      (∀ y ∈ sLocalRingUnitImage K 6 (sourceHilbertSet K S₀),
        sourceRingHilbertForm K hζ (sourceHilbertSet K S₀) x y = 1) ↔
      x ∈ sLocalRingUnitImage K 6 (sourceHilbertSet K S₀) := by
  let e := sLocalRingPowerEquiv K 6 (sourceHilbertSet K S₀)
  intro x
  rw [sLocalRingPowerEquiv_unitImage_iff]
  rw [← source_sixth_whole_unitImage_selfOrthogonal K hζ S₀]
  constructor
  · intro hx y hy
    have hy' : e.symm y ∈ sLocalRingUnitImage K 6 (sourceHilbertSet K S₀) := by
      rw [sLocalRingPowerEquiv_unitImage_iff]
      simpa only [e, MulEquiv.apply_symm_apply] using hy
    have h := hx (e.symm y) hy'
    change sourceWholeHilbertForm K hζ (sourceHilbertSet K S₀) (e x) (e (e.symm y)) = 1 at h
    simpa only [e.apply_symm_apply] using h
  · intro hx y hy
    exact hx (e y) ((sLocalRingPowerEquiv_unitImage_iff K 6 (sourceHilbertSet K S₀) y).mp hy)

end
end ArtinMatthews
