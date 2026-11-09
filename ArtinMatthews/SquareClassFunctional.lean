module

public import ArtinMatthews.Definitions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Prescribing a functional on square classes

The linear-algebra step in Section 10.1 says that assigning the value one to
each generator over `𝔽₂` is consistent exactly when no odd subset sums to zero.
The functional below is constructed by descending a map through its kernel
and then extending it from the span of the generators.
-/

namespace ArtinMatthews

section LinearAlgebra

variable {K ι V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Values on generators extend to a functional precisely when they respect
all finitely supported linear relations. -/
theorem exists_linearFunctional_of_relations (v : ι → V) (w : ι → K)
    (hrel : ∀ c : ι →₀ K,
      Finsupp.linearCombination K v c = 0 → Finsupp.linearCombination K w c = 0) :
    ∃ f : V →ₗ[K] K, ∀ i, f (v i) = w i := by
  let L : (ι →₀ K) →ₗ[K] V := Finsupp.linearCombination K v
  let R : (ι →₀ K) →ₗ[K] K := Finsupp.linearCombination K w
  have hker : L.rangeRestrict.ker ≤ R.ker := by
    rw [LinearMap.ker_rangeRestrict]
    intro c hc
    exact hrel c hc
  let descended : L.range →ₗ[K] K :=
    L.rangeRestrict.liftOfSurjective L.surjective_rangeRestrict ⟨R, hker⟩
  obtain ⟨f, hf⟩ := descended.exists_extend
  refine ⟨f, fun i => ?_⟩
  have hdesc : descended (L.rangeRestrict (Finsupp.single i 1)) =
      R (Finsupp.single i 1) :=
    LinearMap.equivOfSurjective_apply L.surjective_rangeRestrict hker
  have hext := LinearMap.congr_fun hf (L.rangeRestrict (Finsupp.single i 1))
  change f (L (Finsupp.single i 1)) = descended (L.rangeRestrict (Finsupp.single i 1))
    at hext
  simpa [L, R] using hext.trans hdesc

end LinearAlgebra

section CharacteristicTwo

variable {ι V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The consistency condition for setting every generator's value to one. -/
def NoOddZeroSum (v : ι → V) : Prop :=
  ∀ s : Finset ι, Odd s.card → (∑ i ∈ s, v i) ≠ 0

/-- Over `𝔽₂`, each nonzero coefficient equals one. -/
lemma zmod_two_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact (hx rfl).elim
  · rfl

/-- Absence of odd zero sums makes the prescribed value one compatible with
every finitely supported relation. -/
theorem one_values_respect_relations (v : ι → V) (hv : NoOddZeroSum v)
    (c : ι →₀ ZMod 2) (hc : Finsupp.linearCombination (ZMod 2) v c = 0) :
    Finsupp.linearCombination (ZMod 2) (fun _ : ι => (1 : ZMod 2)) c = 0 := by
  classical
  have hc1 : ∀ i ∈ c.support, c i = 1 := by
    intro i hi
    exact zmod_two_eq_one_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  have hsum : (∑ i ∈ c.support, v i) = 0 := by
    calc
      _ = ∑ i ∈ c.support, c i • v i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hc1 i hi, one_smul]
      _ = 0 := hc
  have heven : Even c.support.card := by
    rcases Nat.even_or_odd c.support.card with heven | hodd
    · exact heven
    · exact False.elim (hv c.support hodd hsum)
  have hpar : (c.support.card : ZMod 2) = 0 := heven.natCast_zmod_two
  change (∑ i ∈ c.support, c i • (1 : ZMod 2)) = 0
  calc
    _ = ∑ _i ∈ c.support, (1 : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hc1 i hi, one_smul]
    _ = (c.support.card : ZMod 2) := by simp
    _ = 0 := hpar

/-- The exact finite-relation criterion used to choose the quadratic signs. -/
theorem noOddZeroSum_iff_exists_linearFunctional (v : ι → V) :
    NoOddZeroSum v ↔ ∃ f : V →ₗ[ZMod 2] ZMod 2, ∀ i, f (v i) = 1 := by
  constructor
  · intro hv
    exact exists_linearFunctional_of_relations v (fun _ => 1)
      (one_values_respect_relations v hv)
  · rintro ⟨f, hf⟩ s hs hzero
    have hsum : (s.card : ZMod 2) = 0 := by
      simpa only [map_sum, hf, Finset.sum_const, nsmul_eq_mul, mul_one, map_zero]
        using congrArg f hzero
    exact (Nat.not_even_iff_odd.mpr hs) (ZMod.natCast_eq_zero_iff_even.mp hsum)

end CharacteristicTwo

/-- The rational square-class group, written additively. -/
abbrev RationalSquareClass :=
  Additive ℚˣ ⧸ AddSubgroup.even (Additive ℚˣ)

noncomputable instance rationalSquareClassModule : Module (ZMod 2) RationalSquareClass :=
  QuotientAddGroup.zmodModule (fun x => ⟨x, two_nsmul x⟩)

/-- The class of a nonzero rational, represented by a rational unit. -/
def rationalUnitSquareClass (u : ℚˣ) : RationalSquareClass :=
  QuotientAddGroup.mk' (AddSubgroup.even (Additive ℚˣ)) (Additive.ofMul u)

theorem rationalUnitSquareClass_eq_zero_iff (u : ℚˣ) :
    rationalUnitSquareClass u = 0 ↔ IsSquare u := by
  change ((Additive.ofMul u : Additive ℚˣ) : RationalSquareClass) = 0 ↔ IsSquare u
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_even, even_ofMul_iff]

theorem sum_rationalUnitSquareClass {ι : Type*} (s : Finset ι) (u : ι → ℚˣ) :
    (∑ i ∈ s, rationalUnitSquareClass (u i)) =
      rationalUnitSquareClass (∏ i ∈ s, u i) := by
  unfold rationalUnitSquareClass
  rw [← map_sum, ← ofMul_prod]

/-- A square rational unit represents precisely the paper's nonzero rational
square predicate on an integer. -/
theorem unit_isSquare_iff_rationalSquare {z : ℤ} (u : ℚˣ)
    (hu : (u : ℚ) = z) : IsSquare u ↔ RationalSquare z := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(v : ℚ), Units.ne_zero v, ?_⟩
    rw [pow_two, ← Units.val_mul, ← hv, hu]
  · rintro ⟨q, hq, hqz⟩
    refine ⟨Units.mk0 q hq, ?_⟩
    apply Units.ext
    change (u : ℚ) = q * q
    rw [hu]
    simpa only [pow_two] using hqz.symm

/-- Turn a nonzero integer family into rational units. -/
def integerUnit {ι : Type*} (a : ι → ℤ) (ha : ∀ i, a i ≠ 0) (i : ι) : ℚˣ :=
  Units.mk0 (a i : ℚ) (by exact_mod_cast ha i)

/-- A zero sum of integer square classes is exactly a rational square product. -/
theorem sum_integerSquareClass_eq_zero_iff {ι : Type*} (s : Finset ι)
    (a : ι → ℤ) (ha : ∀ i, a i ≠ 0) :
    (∑ i ∈ s, rationalUnitSquareClass (integerUnit a ha i)) = 0 ↔
      RationalSquare (∏ i ∈ s, a i) := by
  rw [sum_rationalUnitSquareClass, rationalUnitSquareClass_eq_zero_iff]
  apply unit_isSquare_iff_rationalSquare
  simp [integerUnit]

/-- The square class of a member of a finite set of nonzero integer bases. -/
def baseSquareClass {S : Finset ℤ} (hzero : ∀ a ∈ S, a ≠ 0)
    (a : {a // a ∈ S}) : RationalSquareClass :=
  rationalUnitSquareClass
    (integerUnit (fun b : {b // b ∈ S} => b.val) (fun b => hzero b.val b.property) a)

/-- The paper's obstruction (A) is exactly the odd-zero-relation obstruction
among the associated rational square classes. -/
theorem not_obstructionA_iff_noOddZeroSum {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0) :
    ¬ ObstructionA S ↔ NoOddZeroSum (baseSquareClass hzero) := by
  classical
  constructor
  · intro hA s hs hsum
    let e : {a // a ∈ S} ↪ ℤ := ⟨Subtype.val, Subtype.val_injective⟩
    let T : Finset ℤ := s.map e
    apply hA
    refine ⟨T, ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
      exact b.property
    · simpa [T] using hs
    · have hr := (sum_integerSquareClass_eq_zero_iff s
        (fun a : {a // a ∈ S} => a.val)
        (fun a => hzero a.val a.property)).mp hsum
      simpa [T, e, Finset.prod_map] using hr
  · intro hno hA
    obtain ⟨T, hTS, hodd, hr⟩ := hA
    let e : {a // a ∈ T} ↪ {a // a ∈ S} :=
      ⟨fun a => ⟨a.val, hTS a.property⟩,
        fun a b h => Subtype.ext (congrArg (fun x : {a // a ∈ S} => x.val) h)⟩
    let s : Finset {a // a ∈ S} := T.attach.map e
    have hs : Odd s.card := by simpa [s] using hodd
    apply hno s hs
    apply (sum_integerSquareClass_eq_zero_iff s
      (fun a : {a // a ∈ S} => a.val)
      (fun a => hzero a.val a.property)).mpr
    have hprod : (∏ a ∈ s, (a : ℤ)) = ∏ a ∈ T, a := by
      change (∏ a ∈ T.attach.map e, (a : ℤ)) = _
      rw [Finset.prod_map]
      exact Finset.prod_attach T (fun a : ℤ => a)
    rw [hprod]
    exact hr

/-- Exact square-class version of the first paragraph of Section 10.1.
The functional is defined on the entire rational square-class space, so it
already extends the functional on the span of the selected bases. -/
theorem not_obstructionA_iff_exists_squareClassFunctional {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0) :
    ¬ ObstructionA S ↔
      ∃ f : RationalSquareClass →ₗ[ZMod 2] ZMod 2,
        ∀ a : {a // a ∈ S}, f (baseSquareClass hzero a) = 1 := by
  rw [not_obstructionA_iff_noOddZeroSum hzero]
  exact noOddZeroSum_iff_exists_linearFunctional (baseSquareClass hzero)

/-- Admissible bases without obstruction (A) admit the quadratic-sign
functional required by the progression construction. -/
theorem exists_squareClassFunctional {S : Finset ℤ} (hS : AdmissibleBases S)
    (hA : ¬ ObstructionA S) :
    ∃ f : RationalSquareClass →ₗ[ZMod 2] ZMod 2,
      ∀ a : {a // a ∈ S}, f (baseSquareClass (fun a ha => (hS.2 a ha).1) a) = 1 :=
  (not_obstructionA_iff_exists_squareClassFunctional
    (fun a ha => (hS.2 a ha).1)).mp hA

end ArtinMatthews
