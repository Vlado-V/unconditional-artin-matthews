module

public import ArtinMatthews.SquareClassFunctional
public import Mathlib.Algebra.BigOperators.Option


set_option backward.privateInPublic true
@[expose] public section

/-!
# The distinguished minus-three square class

After the odd relations have been excluded, prescribing the value one on an
additional vector fails only when that vector is an even sum of the original
generators.  For rational square classes this gives the two branches in the
quadratic progression construction in Section 10.1.
-/

namespace ArtinMatthews

section CharacteristicTwo

variable {ι V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Adjoining a distinguished generator either permits the value one, or
exhibits that generator as an even subset sum of the old generators. -/
theorem distinguished_functional_or_even_sum (v : ι → V) (d : V)
    (hv : NoOddZeroSum v) :
    (∃ f : V →ₗ[ZMod 2] ZMod 2, (∀ i, f (v i) = 1) ∧ f d = 1) ∨
      ∃ s : Finset ι, Even s.card ∧ (∑ i ∈ s, v i) = d := by
  classical
  let w : Option ι → V := fun i => i.elim d v
  by_cases hw : NoOddZeroSum w
  · obtain ⟨f, hf⟩ := (noOddZeroSum_iff_exists_linearFunctional w).mp hw
    exact Or.inl ⟨f, fun i => hf (some i), hf none⟩
  · right
    simp only [NoOddZeroSum, not_forall, not_not] at hw
    obtain ⟨s, hsodd, hszero⟩ := hw
    have hnone : none ∈ s := by
      by_contra hnone
      apply hv s.eraseNone
      · simpa only [Finset.card_eraseNone_of_not_mem hnone] using hsodd
      · have hmap : s.eraseNone.map Function.Embedding.some = s := by
          simp [Finset.map_some_eraseNone, Finset.erase_eq_of_notMem hnone]
        calc
          (∑ i ∈ s.eraseNone, v i) = ∑ i ∈ s.eraseNone.map Function.Embedding.some, w i := by
            rw [Finset.sum_map]
            rfl
          _ = 0 := by rw [hmap]; exact hszero
    refine ⟨s.eraseNone, ?_, ?_⟩
    · rw [Finset.card_eraseNone_of_mem hnone]
      exact Nat.Odd.sub_odd hsodd (by decide : Odd 1)
    · have hsum : d + (∑ i ∈ s.eraseNone, v i) = 0 := by
        have h := Finset.sum_insertNone w s.eraseNone
        rw [Finset.insertNone_eraseNone, Finset.insert_eq_of_mem hnone] at h
        change (∑ i ∈ s, w i) = d + (∑ i ∈ s.eraseNone, v i) at h
        exact h.symm.trans hszero
      have hdd : d + d = 0 := by
        calc
          d + d = ((1 : ZMod 2) + 1) • d := by rw [add_smul]; simp
          _ = 0 := by change (0 : ZMod 2) • d = 0; exact zero_smul _ _
      have hneg : -d = d := neg_eq_iff_add_eq_zero.mpr hdd
      exact (eq_neg_of_add_eq_zero_right hsum).trans hneg

end CharacteristicTwo

/-- The rational unit represented by minus three. -/
def negativeThreeUnit : ℚˣ := Units.mk0 (-3) (by norm_num)

/-- The distinguished square class controlling the cubic split case. -/
def negativeThreeSquareClass : RationalSquareClass :=
  rationalUnitSquareClass negativeThreeUnit

theorem rationalUnitSquareClass_eq_iff (u v : ℚˣ) :
    rationalUnitSquareClass u = rationalUnitSquareClass v ↔ IsSquare (u / v) := by
  change ((Additive.ofMul u : Additive ℚˣ) : RationalSquareClass) =
      ((Additive.ofMul v : Additive ℚˣ) : RationalSquareClass) ↔ IsSquare (u / v)
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_even]
  exact even_ofMul_iff

theorem unit_class_eq_negativeThree_iff {z : ℤ} (u : ℚˣ)
    (hu : (u : ℚ) = z) :
    rationalUnitSquareClass u = negativeThreeSquareClass ↔
      NegativeThreeRationalSquare z := by
  rw [negativeThreeSquareClass, rationalUnitSquareClass_eq_iff]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(v : ℚ), Units.ne_zero v, ?_⟩
    have hrat : (z : ℚ) / (-3) = (v : ℚ) ^ 2 := by
      have h := congrArg (fun x : ℚˣ => (x : ℚ)) hv
      simpa [hu, negativeThreeUnit, pow_two] using h
    calc
      (z : ℚ) = -3 * ((z : ℚ) / (-3)) := by ring
      _ = -3 * (v : ℚ) ^ 2 := by rw [hrat]
  · rintro ⟨q, hq, hqz⟩
    refine ⟨Units.mk0 q hq, ?_⟩
    apply Units.ext
    change (u : ℚ) / (-3) = q * q
    rw [hu, hqz]
    ring

/-- An even sum equal to the distinguished class yields the precise
negative-three-square relation used in the paper. -/
theorem sum_integerSquareClass_eq_negativeThree_iff {ι : Type*} (s : Finset ι)
    (a : ι → ℤ) (ha : ∀ i, a i ≠ 0) :
    (∑ i ∈ s, rationalUnitSquareClass (integerUnit a ha i)) = negativeThreeSquareClass ↔
      NegativeThreeRationalSquare (∏ i ∈ s, a i) := by
  rw [sum_rationalUnitSquareClass]
  apply unit_class_eq_negativeThree_iff
  simp [integerUnit]

/-- The two cases in Section 10.1: the minus-three value may be set to one,
or an even subset of the bases has product in `-3 ℚ×²`. -/
theorem minus_three_squareClass_dichotomy {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0) (hA : ¬ ObstructionA S) :
    (∃ f : RationalSquareClass →ₗ[ZMod 2] ZMod 2,
      (∀ a : {a // a ∈ S}, f (baseSquareClass hzero a) = 1) ∧
      f negativeThreeSquareClass = 1) ∨
    ∃ T : Finset ℤ, T ⊆ S ∧ Even T.card ∧
      NegativeThreeRationalSquare (∏ a ∈ T, a) := by
  classical
  have hv := (not_obstructionA_iff_noOddZeroSum hzero).mp hA
  rcases distinguished_functional_or_even_sum (baseSquareClass hzero)
      negativeThreeSquareClass hv with hf | ⟨s, hs, hsum⟩
  · exact Or.inl hf
  · right
    let e : {a // a ∈ S} ↪ ℤ := ⟨Subtype.val, Subtype.val_injective⟩
    let T : Finset ℤ := s.map e
    refine ⟨T, ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
      exact b.property
    · simpa [T] using hs
    · have hr := (sum_integerSquareClass_eq_negativeThree_iff s
        (fun a : {a // a ∈ S} => a.val)
        (fun a => hzero a.val a.property)).mp hsum
      simpa [T, e, Finset.prod_map] using hr

end ArtinMatthews
