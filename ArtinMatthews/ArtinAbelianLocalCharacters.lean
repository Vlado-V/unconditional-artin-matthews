module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.GroupTheory.FiniteAbelian.Duality


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite-character local Euler polynomials. The finite product
argument is extracted from OAI PrimePackets/ArtinEuler without its global
ray-continuation dependency. The quotient version retains ramified inertia. -/

noncomputable section
namespace ArtinMatthews.AbelianLocal
open scoped Classical BigOperators

lemma prod_one_sub_rootsOfUnity (n : ℕ) (hn : 0 < n) (z : ℂ) :
    letI : NeZero n := ⟨hn.ne'⟩
    letI : Fintype (rootsOfUnity n ℂ) := Fintype.ofFinite _
    (∏ ζ : rootsOfUnity n ℂ, (1 - (ζ.val : ℂ) * z)) = 1 - z ^ n := by
  let : NeZero n := ⟨hn.ne'⟩
  let : Fintype (rootsOfUnity n ℂ) := Fintype.ofFinite _
  obtain ⟨a, ha⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ n
  let ζ : rootsOfUnity n ℂ := ha.toRootsOfUnity
  have hcoe : (ζ.val : ℂ) = a := rfl
  let e : Fin n ≃ rootsOfUnity n ℂ := Equiv.ofBijective (fun i => ζ ^ i.val) (by
    constructor
    · intro i j hij
      apply Fin.ext
      apply ha.pow_inj i.isLt j.isLt
      have := congrArg (fun x : rootsOfUnity n ℂ => (x.val : ℂ)) hij
      simpa only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hcoe] using this
    · intro b
      have hb : (b.val : ℂ)^n = 1 := by
        simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
          congrArg Units.val ((mem_rootsOfUnity n b.val).mp b.property)
      obtain ⟨i, hi, hbi⟩ := ha.eq_pow_of_pow_eq_one hb
      refine ⟨⟨i, hi⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      simpa only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hcoe] using hbi)
  have hp := congrArg (Polynomial.eval (1 : ℂ))
    (X_pow_sub_C_eq_prod ha hn (rfl : z ^ n = z ^ n))
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, one_pow, Polynomial.eval_prod] at hp
  rw [hp, Finset.prod_range]
  exact (Fintype.prod_equiv e (fun i => 1 - a^i.val * z)
    (fun b => 1 - (b.val : ℂ) * z) (fun i => by
      change 1 - a^i.val * z = 1 - (ζ.val : ℂ)^i.val * z
      rw [hcoe])).symm

lemma prod_comp_surjective_hom {A B : Type*} [CommGroup A] [CommGroup B]
    [Fintype A] [Fintype B] (f : A →* B) (hf : Function.Surjective f) (v : B → ℂ) :
    (∏ a, v (f a)) = (∏ b, v b) ^ Nat.card f.ker := by
  rw [← Fintype.prod_fiberwise' f v, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro b _
  rw [Finset.prod_const, Finset.card_univ]
  congr 1
  exact (Fintype.card_eq_nat_card).trans
    (Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hf b))

lemma zpowers_subtype_generator {G : Type*} [Group G] (g : G) :
    ∀ x : Subgroup.zpowers g,
      x ∈ Subgroup.zpowers (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g) := by
  intro x
  obtain ⟨m, hm⟩ := x.property
  exact ⟨m, Subtype.ext hm⟩

lemma prod_characters_at_generator {H : Type*} [CommGroup H] [Finite H]
    (g : H) (hg : ∀ x : H, x ∈ Subgroup.zpowers g) (z : ℂ) :
    letI : Fintype (H →* ℂˣ) := Fintype.ofFinite _
    (∏ χ : H →* ℂˣ, (1 - (χ g : ℂ) * z)) = 1 - z ^ Nat.card H := by
  let : Fintype (H →* ℂˣ) := Fintype.ofFinite _
  let : Fintype (rootsOfUnity (Nat.card H) ℂ) := Fintype.ofFinite _
  let e := (IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator hg ℂˣ).trans
    (rootsOfUnityUnitsMulEquiv ℂ (Nat.card H))
  rw [← prod_one_sub_rootsOfUnity (Nat.card H) Nat.card_pos z]
  apply Fintype.prod_equiv e.toEquiv
  intro χ
  rfl

lemma prod_characters_at_element {G : Type*} [CommGroup G] [Finite G]
    (g : G) (z : ℂ) :
    letI : Fintype (G →* ℂˣ) := Fintype.ofFinite _
    (∏ χ : G →* ℂˣ, (1 - (χ g : ℂ) * z)) =
      (1 - z ^ orderOf g) ^ Nat.card (G ⧸ Subgroup.zpowers g) := by
  let : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  let H := Subgroup.zpowers g
  let : Fintype (H →* ℂˣ) := Fintype.ofFinite _
  let gH : H := ⟨g, Subgroup.mem_zpowers g⟩
  let r := MonoidHom.domRestrictHom H ℂˣ
  change (∏ χ : G →* ℂˣ, (1 - (r χ gH : ℂ) * z)) = _
  rw [prod_comp_surjective_hom r (MonoidHom.domRestrict_surjective (M := ℂ) H)
    (fun χ : H →* ℂˣ => 1 - (χ gH : ℂ) * z)]
  rw [prod_characters_at_generator gH (zpowers_subtype_generator g),
    CommGroup.card_domRestrictHom_ker (M := ℂ), Nat.card_zpowers]


/-- The local character polynomial on the actual inertia quotient. -/
theorem prod_inertiaQuotient_characters
    {G : Type*} [CommGroup G] [Finite G] (I : Subgroup G) (σ : G) (T : ℂ) :
    letI : Fintype ((G ⧸ I) →* ℂˣ) := Fintype.ofFinite _
    (∏ χ : (G ⧸ I) →* ℂˣ, (1 - (χ (QuotientGroup.mk σ) : ℂ) * T)) =
      (1 - T ^ orderOf (QuotientGroup.mk σ : G ⧸ I)) ^
        Nat.card ((G ⧸ I) ⧸ Subgroup.zpowers (QuotientGroup.mk σ : G ⧸ I)) :=
  prod_characters_at_element (QuotientGroup.mk σ : G ⧸ I) T

/-- Inverting the genuine character polynomial gives its local Euler factor. -/
theorem prod_inertiaQuotient_euler_factors
    {G : Type*} [CommGroup G] [Finite G] (I : Subgroup G) (σ : G) (T : ℂ) :
    letI : Fintype ((G ⧸ I) →* ℂˣ) := Fintype.ofFinite _
    (∏ χ : (G ⧸ I) →* ℂˣ, (1 - (χ (QuotientGroup.mk σ) : ℂ) * T)⁻¹) =
      ((1 - T ^ orderOf (QuotientGroup.mk σ : G ⧸ I))⁻¹) ^
        Nat.card ((G ⧸ I) ⧸ Subgroup.zpowers (QuotientGroup.mk σ : G ⧸ I)) := by
  let : Fintype ((G ⧸ I) →* ℂˣ) := Fintype.ofFinite _
  rw [Finset.prod_inv_distrib, prod_inertiaQuotient_characters, inv_pow]

end ArtinMatthews.AbelianLocal
