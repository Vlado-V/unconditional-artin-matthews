module

public import ArtinMatthews.SLocalIsotropicComplement
public import ArtinMatthews.SLocalWeakApproximation


set_option backward.privateInPublic true
@[expose] public section

/-! The source field and one constructed finite principal set S supply
actual isotropic complements at exponents two and three, including the
characteristic-two linear algebra. The sixth-power CRT join is separate. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.GlobalClassFields SIntegerPrincipalization
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def sourceHilbertSeed (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :=
  S₀ ∪ (sUnitKummerNormSupport (K := K) 2 ∅ ∪
    (sUnitKummerNormSupport (K := K) 3 ∅ ∪ sUnitKummerNormSupport (K := K) 6 ∅))

def sourceHilbertSet (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :=
  principalizingSet (sourceHilbertSeed K S₀)

theorem required_subset_sourceHilbertSet (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    S₀ ⊆ sourceHilbertSet K S₀ :=
  Finset.Subset.trans Finset.subset_union_left (required_subset_principalizingSet _)

theorem normSupport_subset_sourceHilbertSet
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+)
    (hn : n = 2 ∨ n = 3 ∨ n = 6) :
    sUnitKummerNormSupport (K := K) n ∅ ⊆ sourceHilbertSet K S₀ := by
  rcases hn with rfl | rfl | rfl
  · intro v hv
    apply required_subset_principalizingSet (sourceHilbertSeed K S₀)
    exact Finset.mem_union_right _ (Finset.mem_union_left _ hv)
  · intro v hv
    apply required_subset_principalizingSet (sourceHilbertSeed K S₀)
    exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ hv))
  · intro v hv
    apply required_subset_principalizingSet (sourceHilbertSeed K S₀)
    exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ hv))

theorem sourceHilbertSet_isPrincipalIdealRing (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    IsPrincipalIdealRing (IntegerRing (K := K) (sourceHilbertSet K S₀)) :=
  principalIntegerRing_isPrincipalIdealRing _

def sourcePrimitiveUnit (n : ℕ+) {ζ : K} (hζ : IsPrimitiveRoot ζ (n : ℕ)) : Kˣ :=
  (hζ.isUnit n.ne_zero).unit

omit [NumberField K] in
theorem sourcePrimitiveUnit_isPrimitive (n : ℕ+) {ζ : K}
    (hζ : IsPrimitiveRoot ζ (n : ℕ)) : IsPrimitiveRoot (sourcePrimitiveUnit K n hζ) (n : ℕ) :=
  hζ.isUnit_unit n.ne_zero

def sourceHilbertRootTwo {ζ : K} (hζ : IsPrimitiveRoot ζ 12) : Kˣ :=
  sourcePrimitiveUnit K 2 (hζ.pow_of_dvd (p := 6) (by decide) (by decide))

def sourceHilbertRootThree {ζ : K} (hζ : IsPrimitiveRoot ζ 12) : Kˣ :=
  sourcePrimitiveUnit K 3 (hζ.pow_of_dvd (p := 4) (by decide) (by decide))

def sourceHilbertRootSix {ζ : K} (hζ : IsPrimitiveRoot ζ 12) : Kˣ :=
  sourcePrimitiveUnit K 6 (hζ.pow_of_dvd (p := 2) (by decide) (by decide))

omit [NumberField K] in
theorem sourceHilbertRootTwo_isPrimitive {ζ : K} (hζ : IsPrimitiveRoot ζ 12) :
    IsPrimitiveRoot (sourceHilbertRootTwo K hζ) 2 := sourcePrimitiveUnit_isPrimitive K 2 _

omit [NumberField K] in
theorem sourceHilbertRootThree_isPrimitive {ζ : K} (hζ : IsPrimitiveRoot ζ 12) :
    IsPrimitiveRoot (sourceHilbertRootThree K hζ) 3 := sourcePrimitiveUnit_isPrimitive K 3 _

omit [NumberField K] in
theorem sourceHilbertRootSix_isPrimitive {ζ : K} (hζ : IsPrimitiveRoot ζ 12) :
    IsPrimitiveRoot (sourceHilbertRootSix K hζ) 6 := sourcePrimitiveUnit_isPrimitive K 6 _

theorem source_isTotallyComplex {ζ : K} (hζ : IsPrimitiveRoot ζ 12) :
    NumberField.IsTotallyComplex K :=
  NumberField.nrRealPlaces_eq_zero_iff.mp
    (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by decide) hζ)

instance sourceHilbertTwoModule (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Module (ZMod 2) (Additive (SLocalPowerClasses K 2 S)) :=
  sLocalPowerClasses_zmodModule K 2 S

instance sourceHilbertThreeModule (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Module (ZMod 3) (Additive (SLocalPowerClasses K 3 S)) :=
  sLocalPowerClasses_zmodModule K 3 S

theorem source_two_three_isotropic_complements {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (B₂ : Submodule (ZMod 2) (Additive (SLocalPowerClasses K 2 (sourceHilbertSet K S₀))))
      (B₃ : Submodule (ZMod 3) (Additive (SLocalPowerClasses K 3 (sourceHilbertSet K S₀)))),
      IsCompl (sUnitPowerSubmodule K 2 (sourceHilbertSet K S₀)) B₂ ∧
      IsCompl (sUnitPowerSubmodule K 3 (sourceHilbertSet K S₀)) B₃ ∧
      (∀ x ∈ B₂, ∀ y ∈ B₂,
        sLocalHilbertForm K 2 (sLocalPrimitiveRoots K 2 (sourceHilbertRootTwo_isPrimitive K hζ))
          (sourceHilbertSet K S₀) (Additive.toMul x) (Additive.toMul y) = 1) ∧
      (∀ x ∈ B₃, ∀ y ∈ B₃,
        sLocalHilbertForm K 3 (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ))
          (sourceHilbertSet K S₀) (Additive.toMul x) (Additive.toMul y) = 1) := by
  let : NumberField.IsTotallyComplex K := source_isTotallyComplex K hζ
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨B₂, hC₂, hI₂⟩ := sLocal_exists_isotropic_complement K 2
    (sourceHilbertRootTwo_isPrimitive K hζ) (neg_one_is_square_of_primitive_twelve K hζ)
    (sourceHilbertSet K S₀) (normSupport_subset_sourceHilbertSet K S₀ 2 (Or.inl rfl))
  obtain ⟨B₃, hC₃, hI₃⟩ := sLocal_exists_isotropic_complement K 3
    (sourceHilbertRootThree_isPrimitive K hζ) (neg_one_is_cube_of_primitive_twelve K hζ)
    (sourceHilbertSet K S₀) (normSupport_subset_sourceHilbertSet K S₀ 3 (Or.inr (Or.inl rfl)))
  exact ⟨B₂, B₃, hC₂, hC₃, hI₂, hI₃⟩

end
end ArtinMatthews
