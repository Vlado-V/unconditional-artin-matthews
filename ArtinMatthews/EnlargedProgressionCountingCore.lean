module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Actual unit-class CRT equivalences and counts with independent local restrictions. -/

namespace ArtinMatthews

open scoped Function

noncomputable def crtUnitsEquiv {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hc : Pairwise (Nat.Coprime on a)) :
    (ZMod (∏ i, a i))ˣ ≃* ∀ i, (ZMod (a i))ˣ :=
  (Units.mapEquiv (ZMod.prodEquivPi a hc).toMulEquiv).trans MulEquiv.piUnits

theorem crtUnitsEquiv_apply {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hc : Pairwise (Nat.Coprime on a)) (u : (ZMod (∏ i, a i))ˣ) (i : ι) :
    crtUnitsEquiv a hc u i =
      Units.map (ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i))
        (ZMod (a i))).toMonoidHom u := by
  apply Units.ext
  exact ZMod.prodEquivPi_apply a hc u i

noncomputable def crtUnitsEquivOfEq {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hc : Pairwise (Nat.Coprime on a)) {N : ℕ} (hN : N = ∏ i, a i) :
    (ZMod N)ˣ ≃* ∀ i, (ZMod (a i))ˣ :=
  (Units.mapEquiv (ZMod.ringEquivCongr hN).toMulEquiv).trans (crtUnitsEquiv a hc)

theorem crtUnitsEquivOfEq_apply {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hc : Pairwise (Nat.Coprime on a)) {N : ℕ} (hN : N = ∏ i, a i)
    (u : (ZMod N)ˣ) (i : ι) :
    crtUnitsEquivOfEq a hc hN u i =
      Units.map (ZMod.castHom (hN.symm ▸ Finset.dvd_prod_of_mem a (Finset.mem_univ i))
        (ZMod (a i))).toMonoidHom u := by
  subst N
  apply Units.ext
  change (ZMod.prodEquivPi a hc (ZMod.ringEquivCongr rfl (u : ZMod (∏ i, a i)))) i = _
  rw [ZMod.ringEquivCongr_refl_apply]
  exact ZMod.prodEquivPi_apply a hc u i

noncomputable def allowedUnitEquiv {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hc : Pairwise (Nat.Coprime on a)) {N : ℕ} (hN : N = ∏ i, a i)
    (V : ∀ i, Finset (ZMod (a i))ˣ) :
    {u : (ZMod N)ˣ // ∀ i, crtUnitsEquivOfEq a hc hN u i ∈ V i} ≃
      ∀ i, {v : (ZMod (a i))ˣ // v ∈ V i} where
  toFun u i := ⟨crtUnitsEquivOfEq a hc hN u.val i, u.property i⟩
  invFun v := ⟨(crtUnitsEquivOfEq a hc hN).symm (fun i => (v i).val), by
    intro i
    simp⟩
  left_inv u := by
    apply Subtype.ext
    exact (crtUnitsEquivOfEq a hc hN).symm_apply_apply u.val
  right_inv v := by
    funext i
    apply Subtype.ext
    exact congrFun ((crtUnitsEquivOfEq a hc hN).apply_symm_apply (fun j => (v j).val)) i

noncomputable def allowedUnitClasses {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hc : Pairwise (Nat.Coprime on a)) {N : ℕ} [NeZero N] (hN : N = ∏ i, a i)
    (V : ∀ i, Finset (ZMod (a i))ˣ) : Finset (ZMod N)ˣ := by
  classical
  exact Finset.univ.filter fun u => ∀ i, crtUnitsEquivOfEq a hc hN u i ∈ V i

@[simp] theorem mem_allowedUnitClasses {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hc : Pairwise (Nat.Coprime on a)) {N : ℕ} [NeZero N] (hN : N = ∏ i, a i)
    (V : ∀ i, Finset (ZMod (a i))ˣ) (u : (ZMod N)ˣ) :
    u ∈ allowedUnitClasses a hc hN V ↔ ∀ i, crtUnitsEquivOfEq a hc hN u i ∈ V i := by
  classical
  simp [allowedUnitClasses]

theorem card_allowedUnitClasses {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hc : Pairwise (Nat.Coprime on a)) {N : ℕ} [NeZero N] (hN : N = ∏ i, a i)
    (V : ∀ i, Finset (ZMod (a i))ˣ) :
    (allowedUnitClasses a hc hN V).card = ∏ i, (V i).card := by
  classical
  rw [← Fintype.card_coe]
  let e : (allowedUnitClasses a hc hN V) ≃
      {u : (ZMod N)ˣ // ∀ i, crtUnitsEquivOfEq a hc hN u i ∈ V i} :=
    Equiv.subtypeEquivRight (fun u => mem_allowedUnitClasses a hc hN V u)
  rw [Fintype.card_congr e, Fintype.card_congr (allowedUnitEquiv a hc hN V), Fintype.card_pi]
  simp only [Fintype.card_coe]

end ArtinMatthews
