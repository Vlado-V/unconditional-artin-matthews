module

public import ArtinMatthews.FiniteFieldNormCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical power-residue characters commute with the actual finite-
field norm. The character and its exact order are constructed here; the
Jacobi-sum Davenport--Hasse identity is not an assumption or conclusion. -/
namespace ArtinMatthews.FiniteFieldCharacter
open scoped Classical
noncomputable section
variable (F : Type*) [Field F] [Finite F]

def powerResidueCharacter (n : ℕ) : MulChar F F :=
  MulChar.ofUnitHom (powMonoidHom ((Nat.card F-1)/n))

omit [Finite F] in
theorem powerResidueCharacter_unit (n : ℕ) (x : Fˣ) :
    powerResidueCharacter F n (x : F) = (x : F)^((Nat.card F-1)/n) := by
  rw [powerResidueCharacter,MulChar.ofUnitHom_coe]
  rfl

omit [Finite F] in
theorem powerResidueCharacter_nonzero (n : ℕ) (x : F) (hx : x ≠ 0) :
    powerResidueCharacter F n x = x^((Nat.card F-1)/n) :=
  powerResidueCharacter_unit F n (Units.mk0 x hx)

theorem powerResidueCharacter_pow (n : ℕ) (hn : n ∣ Nat.card F-1) :
    powerResidueCharacter F n ^ n = 1 := by
  let : Fintype F := Fintype.ofFinite F
  apply MulChar.ext
  intro x
  rw [MulChar.pow_apply_coe,powerResidueCharacter_unit,← pow_mul,Nat.div_mul_cancel hn,
    MulChar.one_apply_coe]
  simpa only [Fintype.card_eq_nat_card] using FiniteField.pow_card_sub_one_eq_one (x : F) x.ne_zero

theorem powerResidueCharacter_orderOf (n : ℕ) (hn : n ∣ Nat.card F-1) :
    orderOf (powerResidueCharacter F n) = n := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgord : orderOf g = Nat.card F-1 :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).trans (Nat.card_units F)
  have hg0 : orderOf g ≠ 0 := by
    rw [hgord]
    exact (Nat.sub_pos_of_lt Finite.one_lt_card).ne'
  have hv : orderOf (g^((Nat.card F-1)/n)) = n := by
    rw [← hgord]
    exact orderOf_pow_orderOf_div hg0 (by simpa only [hgord] using hn)
  let ev : MulChar F F →* Fˣ :=
    { toFun := fun χ => χ.toUnitHom g
      map_one' := by apply Units.ext; exact MulChar.one_apply_coe g
      map_mul' := by intro χ θ; apply Units.ext; rfl }
  have he : ev (powerResidueCharacter F n) = g^((Nat.card F-1)/n) := by
    apply Units.ext
    exact powerResidueCharacter_unit F n g
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one (powerResidueCharacter_pow F n hn)
  · have h := orderOf_map_dvd ev (powerResidueCharacter F n)
    rwa [he,hv] at h

variable (E : Type*) [Field E] [Finite E] [Algebra F E]

omit [Finite F] [Finite E] in
theorem card_sub_one_dvd_extension : Nat.card F-1 ∣ Nat.card E-1 := by
  have h := Subgroup.card_dvd_of_injective (Units.map (algebraMap F E).toMonoidHom) (by
    intro u v huv
    apply Units.ext
    exact (algebraMap F E).injective (congrArg (fun x : Eˣ => (x : E)) huv))
  simpa only [Nat.card_units] using h

omit [Finite F] in
theorem norm_power_residue (n : ℕ) (hn : n ∣ Nat.card F-1) (x : E) :
    algebraMap F E ((Algebra.norm F x)^((Nat.card F-1)/n)) = x^((Nat.card E-1)/n) := by
  rw [map_pow,FiniteField.algebraMap_norm_eq_pow,← pow_mul,
    Nat.div_mul_div (card_sub_one_dvd_extension F E) hn]

omit [Finite F] in
theorem powerResidueCharacter_norm_lift (n : ℕ) (hn : n ∣ Nat.card F-1) :
    (normLift F E (powerResidueCharacter F n)).ringHomComp (algebraMap F E) =
      powerResidueCharacter E n := by
  apply MulChar.ext
  intro x
  rw [MulChar.ringHomComp_apply,normLift_apply,
    powerResidueCharacter_nonzero F n _ (Algebra.norm_ne_zero_iff.mpr x.ne_zero),
    powerResidueCharacter_unit E n x]
  exact norm_power_residue F E n hn (x : E)

omit [Finite F] in
theorem powerResidueCharacter_extension_order (n : ℕ) (hn : n ∣ Nat.card F-1) :
    orderOf (powerResidueCharacter E n) = n :=
  powerResidueCharacter_orderOf E n (hn.trans (card_sub_one_dvd_extension F E))

end
end ArtinMatthews.FiniteFieldCharacter
