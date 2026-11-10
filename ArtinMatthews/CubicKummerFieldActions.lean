module

public import ArtinMatthews.CubicKummerFieldBase
public import ArtinMatthews.CubicKummerFieldRoots
public import Mathlib.Analysis.InnerProductSpace.Basic
public import ArtinMatthews.CubicAbelianIntersection
public import ArtinMatthews.CubicKummerFieldActionCore
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Actual cubic automorphisms and complex conjugation on the concrete splitting field. -/

namespace ArtinMatthews

/-- The cubic cyclotomic base viewed inside the concrete splitting field. -/
noncomputable def cubicKummerBase (S : Finset ℚ) : IntermediateField ℚ (cubicKummerField S) :=
  cubicCyclotomicField.comap (cubicKummerField S).val

/-- Complex conjugation restricted to the actual normal splitting field. -/
noncomputable def cubicKummerConjugation (S : Finset ℚ) :
    Gal(cubicKummerField S/ℚ) :=
  (Complex.conjAe.restrictScalars ℚ).restrictNormal (cubicKummerField S)

theorem coe_cubicKummerConjugation (S : Finset ℚ) (x : cubicKummerField S) :
    ((cubicKummerConjugation S x : cubicKummerField S) : ℂ) = star (x : ℂ) := by
  exact (Complex.conjAe.restrictScalars ℚ).restrictNormal_commutes (cubicKummerField S) x

theorem cubicKummerConjugation_sq (S : Finset ℚ) : cubicKummerConjugation S ^ 2 = 1 := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  change ((cubicKummerConjugation S (cubicKummerConjugation S x) : cubicKummerField S) : ℂ) = x
  rw [coe_cubicKummerConjugation, coe_cubicKummerConjugation, star_star]

theorem cubicKummerConjugation_inv (S : Finset ℚ) :
    (cubicKummerConjugation S)⁻¹ = cubicKummerConjugation S :=
  inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using cubicKummerConjugation_sq S)

/-- The cubic cyclotomic field is contained in the splitting field. -/
theorem cubicCyclotomicField_le_cubicKummerField (S : Finset ℚ) :
    cubicCyclotomicField ≤ cubicKummerField S := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro z hz
  have : z = cubicZeta := Set.mem_singleton_iff.mp hz
  subst z
  exact cube_unity_mem_cubicKummerField S cubicZeta_pow_three

/-- Fixing the cubic base fixes every cube root of unity, not just the chosen generator. -/
theorem cubicKummer_aut_fixes_cube_roots {S : Finset ℚ}
    {σ : Gal(cubicKummerField S/ℚ)} (hσ : σ ∈ (cubicKummerBase S).fixingSubgroup)
    (r : cubicKummerField S) (hr : r ^ 3 = 1) : σ r = r := by
  have hrC : (r : ℂ) ^ 3 = 1 := by exact_mod_cast hr
  have hrF : (r : ℂ) ∈ cubicCyclotomicField := cube_unity_mem_cubicCyclotomicField hrC
  exact (IntermediateField.mem_fixingSubgroup_iff (cubicKummerBase S) σ).mp hσ r hrF

/-- Conjugation inverts every cube root of unity in the splitting field. -/
theorem cubicKummer_conjugation_cube_roots (S : Finset ℚ)
    (r : cubicKummerField S) (hr : r ^ 3 = 1) :
    cubicKummerConjugation S r = r⁻¹ := by
  apply Subtype.ext
  rw [coe_cubicKummerConjugation]
  exact conj_eq_inv_of_cube_eq_one (by exact_mod_cast hr)

/-- Every generator has its cube in the rational base field. -/
theorem cubicKummer_generator_cube_rational {S : Finset ℚ} {z : ℂ}
    (hz : z ∈ (cubicKummerPolynomial S).rootSet ℂ) :
    ∃ a : ℚ, (⟨z, IntermediateField.subset_adjoin ℚ _ hz⟩ : cubicKummerField S) ^ 3 =
      algebraMap ℚ (cubicKummerField S) a := by
  rcases (mem_cubicKummerPolynomial_rootSet_iff S z).mp hz with h | ⟨a, _, h⟩
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using h
  · refine ⟨a, ?_⟩
    apply Subtype.ext
    exact h

/-- The actual relative automorphism group has exponent dividing three. -/
theorem cubicKummer_aut_cube_eq_one {S : Finset ℚ}
    {σ : Gal(cubicKummerField S/ℚ)} (hσ : σ ∈ (cubicKummerBase S).fixingSubgroup) :
    σ ^ 3 = 1 := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.adjoin_algHom_ext ℚ
  intro z hz
  obtain ⟨a, ha⟩ := cubicKummer_generator_cube_rational hz
  exact aut_cube_apply_of_fixed_cube_roots σ (cubicKummer_aut_fixes_cube_roots hσ) ha

/-- Actual complex conjugation acts by inversion on the cubic relative Galois group. -/
theorem cubicKummer_conjugation_inverts {S : Finset ℚ}
    {σ : Gal(cubicKummerField S/ℚ)} (hσ : σ ∈ (cubicKummerBase S).fixingSubgroup) :
    cubicKummerConjugation S * σ * (cubicKummerConjugation S)⁻¹ = σ⁻¹ := by
  rw [cubicKummerConjugation_inv]
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.adjoin_algHom_ext ℚ
  intro z hz
  obtain ⟨a, ha⟩ := cubicKummer_generator_cube_rational hz
  exact conjugate_aut_apply_of_cubic_radical σ (cubicKummerConjugation S)
    (cubicKummer_aut_fixes_cube_roots hσ) (cubicKummer_conjugation_cube_roots S) ha

/-- The concrete rational cubic radical compositum has no additional
intersection with any cyclotomic field of conductor divisible by three. -/
theorem cubicKummer_cyclotomic_intersection (S : Finset ℚ)
    (L : IntermediateField ℚ ℂ) (M : ℕ) [NeZero M]
    [IsCyclotomicExtension {M} ℚ L] (hM : 3 ∣ M) :
    cubicKummerField S ⊓ L = cubicCyclotomicField := by
  exact cubic_cyclotomic_intersection_eq (cubicKummerField S) cubicCyclotomicField L M
    (cubicCyclotomicField_le_cubicKummerField S) hM (cubicKummerConjugation S)
    (fun _ hσ => cubicKummer_aut_cube_eq_one hσ)
    (fun _ hσ => cubicKummer_conjugation_inverts hσ)

end ArtinMatthews
