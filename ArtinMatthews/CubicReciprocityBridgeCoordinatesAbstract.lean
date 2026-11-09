module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Generating finite character groups by separating coordinates

A family of characters separating points of a finite abelian group generates
its full character group. If the coordinate characters are cubic, every
character has exponents in `{0,1,2}`.
-/

open scoped BigOperators

namespace ArtinMatthews

/-- Integer exponent products of a finite family of unit-valued characters. -/
noncomputable def coordinateCharacterProduct
    {ι G : Type*} [Fintype ι] [CommGroup G]
    (c : ι → G →* ℂˣ) : Multiplicative (ι → ℤ) →* (G →* ℂˣ) where
  toFun z :=
    { toFun g := ∏ i, (c i g) ^ (z.toAdd i)
      map_one' := by simp
      map_mul' g h := by simp only [map_mul, mul_zpow, Finset.prod_mul_distrib] }
  map_one' := by
    apply MonoidHom.ext
    intro g
    change (∏ i, (c i g) ^ (0 : ℤ)) = 1
    simp
  map_mul' z w := by
    apply MonoidHom.ext
    intro g
    change (∏ i, (c i g) ^ (z.toAdd i + w.toAdd i)) = _
    simp only [zpow_add, MonoidHom.mul_apply, Finset.prod_mul_distrib]
    rfl

theorem separating_characters_generate
    {ι G : Type*} [Fintype ι] [CommGroup G] [Finite G]
    (c : ι → G →* ℂˣ)
    (hsep : Function.Injective (fun g => fun i => c i g))
    (χ : G →* ℂˣ) :
    ∃ z : ι → ℤ, ∀ g, χ g = ∏ i, (c i g) ^ (z i) := by
  classical
  let H := (coordinateCharacterProduct c).range
  have hcoord (i : ι) : c i ∈ H := by
    refine ⟨Multiplicative.ofAdd (fun j => if i = j then (1 : ℤ) else 0), ?_⟩
    apply MonoidHom.ext
    intro g
    change (∏ j, (c j g) ^ (if i = j then (1 : ℤ) else 0)) = c i g
    simp
  let e := CommGroup.subgroupOrderIsoSubgroupMonoidHom G ℂ
  have he : e.symm (OrderDual.toDual H) = ⊥ := by
    ext g
    change g ∈ (CommGroup.subgroupOrderIsoSubgroupMonoidHom G ℂ).symm
      (OrderDual.toDual H) ↔ _
    rw [CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff]
    constructor
    · intro hg
      change g = 1
      apply hsep
      funext i
      simpa using hg (c i) (hcoord i)
    · intro hg
      rw [Subgroup.mem_bot] at hg
      subst g
      simp
  have htop : H = ⊤ := by
    apply e.symm.injective
    change e.symm (OrderDual.toDual H) = e.symm ⊥
    rw [he, e.symm.map_bot]
  obtain ⟨z, hz⟩ := (MonoidHom.range_eq_top.mp htop) χ
  refine ⟨z.toAdd, ?_⟩
  intro g
  exact (DFunLike.congr_fun hz g).symm

lemma zpow_eq_pow_mod_three {A : Type*} [Group A] {u : A}
    (hu : u ^ 3 = 1) (z : ℤ) : u ^ z = u ^ (z % 3).toNat := by
  have hn : 0 ≤ z % 3 := Int.emod_nonneg _ (by norm_num : (3 : ℤ) ≠ 0)
  have hu' : u ^ (3 : ℤ) = 1 := by simpa only [zpow_ofNat] using hu
  have hmod : u ^ z = u ^ (z % 3) := by
    calc
      u ^ z = u ^ (z % 3 + 3 * (z / 3)) :=
        congrArg (fun n : ℤ => u ^ n) (Int.emod_add_mul_ediv z 3).symm
      _ = u ^ (z % 3) := by rw [zpow_add, zpow_mul, hu', one_zpow, mul_one]
  rw [hmod, ← zpow_natCast, Int.toNat_of_nonneg hn]

/-- Separating cubic coordinates generate every character, with each exponent
chosen in the canonical three-element range. -/
theorem separating_cubic_characters_generate
    {ι G : Type*} [Fintype ι] [CommGroup G] [Finite G]
    (c : ι → G →* ℂˣ)
    (hcube : ∀ i g, (c i g) ^ 3 = 1)
    (hsep : Function.Injective (fun g => fun i => c i g))
    (χ : G →* ℂˣ) :
    ∃ e : ι → Fin 3, ∀ g, χ g = ∏ i, (c i g) ^ (e i : ℕ) := by
  obtain ⟨z, hz⟩ := separating_characters_generate c hsep χ
  let e : ι → Fin 3 := fun i => ⟨(z i % 3).toNat, by
    have hlo : 0 ≤ z i % 3 := Int.emod_nonneg _ (by norm_num : (3 : ℤ) ≠ 0)
    have hhi : z i % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num : (0 : ℤ) < 3)
    omega⟩
  refine ⟨e, fun g => (hz g).trans ?_⟩
  apply Finset.prod_congr rfl
  intro i _
  exact zpow_eq_pow_mod_three (hcube i g) (z i)

end ArtinMatthews
