module

public import ArtinMatthews.CubicFrobeniusIntegral
public import ArtinMatthews.CubicKummerFieldActions
public import ArtinMatthews.Definitions
public import ArtinMatthews.CubicFrobeniusCondition
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Nonempty inversion-stable cubic Frobenius conditions on the actual Kummer field. -/

open scoped NumberField

namespace ArtinMatthews

/-- Integer bases viewed as rational radicands. -/
def integerCubicBases (S : Finset ℤ) : Finset ℚ := S.image (fun a : ℤ => (a : ℚ))

/-- The concrete cubic splitting field associated to integer bases. -/
noncomputable abbrev integerCubicField (S : Finset ℤ) := cubicKummerField (integerCubicBases S)

noncomputable instance integerCubicField_numberField (S : Finset ℤ) :
    NumberField (integerCubicField S) := {}

/-- The actual subgroup fixing the cubic cyclotomic base. -/
noncomputable abbrev integerCubicGaloisGroup (S : Finset ℤ) :=
  (cubicKummerBase (integerCubicBases S)).fixingSubgroup

/-- The preferred primitive cube root of unity as an element of the Kummer field. -/
noncomputable def kummerCubicZeta (B : Finset ℚ) : cubicKummerField B :=
  ⟨cubicZeta, cube_unity_mem_cubicKummerField B cubicZeta_pow_three⟩

theorem kummerCubicZeta_pow_three (B : Finset ℚ) : (kummerCubicZeta B) ^ 3 = 1 := by
  apply Subtype.ext
  exact cubicZeta_pow_three

/-- Fixing the explicit primitive cubic root fixes the whole cyclotomic base. -/
theorem cubicKummer_mem_fixingSubgroup_of_zeta {B : Finset ℚ}
    (σ : Gal(cubicKummerField B/ℚ)) (hζ : σ (kummerCubicZeta B) = kummerCubicZeta B) :
    σ ∈ (cubicKummerBase B).fixingSubgroup := by
  let i : cubicCyclotomicField →ₐ[ℚ] cubicKummerField B :=
    IntermediateField.inclusion (cubicCyclotomicField_le_cubicKummerField B)
  have heq : σ.toAlgHom.comp i = i := by
    apply IntermediateField.adjoin_algHom_ext ℚ
    intro z hz
    have hzeta : z = cubicZeta := Set.mem_singleton_iff.mp hz
    subst z
    exact hζ
  apply (IntermediateField.mem_fixingSubgroup_iff (cubicKummerBase B) σ).mpr
  intro x hx
  exact AlgHom.congr_fun heq ⟨(x : ℂ), hx⟩

/-- Every selected integer really has a cubic root in the constructed field. -/
theorem exists_integerCubicField_root {S : Finset ℤ} {a : ℤ} (ha : a ∈ S) :
    ∃ x : integerCubicField S, x ^ 3 = (a : integerCubicField S) := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ) (by decide : 0 < 3)
  have haQ : (a : ℚ) ∈ integerCubicBases S := Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hzQ : z ^ 3 = ((a : ℚ) : ℂ) := by simpa using hz
  refine ⟨⟨z, cube_root_mem_cubicKummerField haQ hzQ⟩, ?_⟩
  apply Subtype.ext
  exact hz

/-- The cubic conjugacy condition: no cube root of any selected base is fixed.
For elements fixing `ζ₃`, this is independent of the choice of each cube root. -/
def cubicNonfixingSet (S : Finset ℤ) : Set (integerCubicGaloisGroup S) :=
  {σ | ∀ a ∈ S, ∀ x : integerCubicField S, x ^ 3 = (a : integerCubicField S) → σ.val x ≠ x}

/-- Over the cubic cyclotomic base, fixing one nonzero root of a cubic is
equivalent to fixing any other root. -/
theorem cubicKummer_fixed_root_iff {B : Finset ℚ} {σ : Gal(cubicKummerField B/ℚ)}
    (hσ : σ ∈ (cubicKummerBase B).fixingSubgroup)
    {x y : cubicKummerField B} (hy0 : y ≠ 0) (hxy : x ^ 3 = y ^ 3) :
    σ x = x ↔ σ y = y := by
  have hx0 : x ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by decide)] at hxy
    exact (pow_ne_zero 3 hy0) hxy.symm
  let t : cubicKummerField B := x / y
  have ht3 : t ^ 3 = 1 := by
    dsimp [t]
    rw [div_pow, hxy, div_self (pow_ne_zero 3 hy0)]
  have ht0 : t ≠ 0 := div_ne_zero hx0 hy0
  have htfix : σ t = t := cubicKummer_aut_fixes_cube_roots hσ t ht3
  have htx : t * y = x := div_mul_cancel₀ x hy0
  have hσx : σ x = t * σ y := by rw [← htx, map_mul, htfix]
  constructor
  · intro hfix
    apply mul_left_cancel₀ ht0
    exact hσx.symm.trans (hfix.trans htx.symm)
  · intro hfix
    rw [hfix] at hσx
    exact hσx.trans htx

/-- Thus the all-root formulation is exactly the condition obtained by
choosing one cube root for every base, including the real cube-root choices
used in the paper. -/
theorem cubicNonfixingSet_iff_chosen_roots {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0)
    (r : {a // a ∈ S} → integerCubicField S)
    (hr : ∀ a, (r a) ^ 3 = (a.val : integerCubicField S))
    (σ : integerCubicGaloisGroup S) :
    σ ∈ cubicNonfixingSet S ↔ ∀ a, σ.val (r a) ≠ r a := by
  constructor
  · intro h a
    exact h a.val a.property (r a) (hr a)
  · intro h a ha x hx hfix
    let i : {a // a ∈ S} := ⟨a, ha⟩
    have haK : (a : integerCubicField S) ≠ 0 := by exact_mod_cast hzero a ha
    have hr0 : r i ≠ 0 := by
      intro hzero
      have hh := hr i
      rw [hzero, zero_pow (by decide)] at hh
      exact haK hh.symm
    apply h i
    exact (cubicKummer_fixed_root_iff σ.property hr0 (hx.trans (hr i).symm)).mp hfix

theorem cubicNonfixingSet_inv {S : Finset ℤ} {σ : integerCubicGaloisGroup S}
    (hσ : σ ∈ cubicNonfixingSet S) : σ⁻¹ ∈ cubicNonfixingSet S := by
  intro a ha x hx hfix
  apply hσ a ha x hx
  have hh := congrArg (fun y : integerCubicField S => σ.val y) hfix
  simpa using hh.symm

/-- The genuine integral Frobenius lift lies in the subgroup fixing the cubic
base whenever the rational prime is one modulo three. -/
noncomputable def relativeCubicFrobenius {S : Finset ℤ} {p : ℕ} [Fact p.Prime]
    (D : IntegralFrobeniusData (integerCubicField S) p) (hp3 : p % 3 = 1) :
    integerCubicGaloisGroup S := by
  let : D.primeIdeal.IsMaximal := D.maximal
  let : CharP ((𝓞 (integerCubicField S)) ⧸ D.primeIdeal) p := D.residue_charP
  have hζ : D.frobenius (kummerCubicZeta (integerCubicBases S)) =
      kummerCubicZeta (integerCubicBases S) :=
    arithFrob_fixes_cube_unity D.primeIdeal D.base_residue_card D.frobenius
      D.frobenius_spec hp3 (kummerCubicZeta_pow_three _)
  exact ⟨D.frobenius, cubicKummer_mem_fixingSubgroup_of_zeta D.frobenius hζ⟩

/-- Membership in the constructed condition is exactly the simultaneous
noncube condition, for the actual characteristic-zero Frobenius lift. -/
theorem relativeCubicFrobenius_mem_iff {S : Finset ℤ} {p : ℕ} [Fact p.Prime]
    (D : IntegralFrobeniusData (integerCubicField S) p) (hp3 : p % 3 = 1)
    (ha0 : ∀ a ∈ S, (a : ZMod p) ≠ 0) :
    relativeCubicFrobenius D hp3 ∈ cubicNonfixingSet S ↔
      ∀ a ∈ S, ¬ IsCubeMod p a := by
  let : D.primeIdeal.IsMaximal := D.maximal
  let : CharP ((𝓞 (integerCubicField S)) ⧸ D.primeIdeal) p := D.residue_charP
  constructor
  · intro h a ha hcube
    obtain ⟨x, hx⟩ := exists_integerCubicField_root ha
    exact h a ha x hx ((arithFrob_fixes_cubeRoot_iff D.primeIdeal D.base_residue_card
      D.frobenius D.frobenius_spec hp3 hx (ha0 a ha)).mpr hcube)
  · intro h a ha x hx
    exact arithFrob_moves_cubeRoot D.primeIdeal D.base_residue_card D.frobenius
      D.frobenius_spec hx (h a ha)

/-- The prime-field noncube witness produces an element of the actual
relative Kummer Galois group moving all cubic roots simultaneously. -/
theorem cubicNonfixingSet_nonempty_of_prime {S : Finset ℤ} {p : ℕ}
    (hp : p.Prime) (hp3 : p % 3 = 1) (hno : ∀ a ∈ S, ¬ IsCubeMod p a) :
    (cubicNonfixingSet S).Nonempty := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨D⟩ := exists_integralFrobeniusData (integerCubicField S) hp
  refine ⟨relativeCubicFrobenius D hp3, ?_⟩
  exact (relativeCubicFrobenius_mem_iff D hp3
    (fun a ha => noncube_mod_ne_zero (hno a ha))).mpr hno

/-- The hypotheses entering the split branch of Section 10.1 give a nonempty
inversion-stable Frobenius condition without assuming a lifting theorem. -/
theorem cubicNonfixingSet_nonempty {S : Finset ℤ} (hB : ¬ ObstructionB S)
    (hrel : ∃ T : Finset ℤ, T ⊆ S ∧ Even T.card ∧
      NegativeThreeRationalSquare (∏ a ∈ T, a)) :
    (cubicNonfixingSet S).Nonempty := by
  obtain ⟨p, hp, hp3, hno⟩ := exists_noncube_prime_of_not_obstructionB hB hrel
  exact cubicNonfixingSet_nonempty_of_prime hp hp3 hno

end ArtinMatthews
