module

public import ArtinMatthews.SourceRowTwistDyadicFamily


set_option backward.privateInPublic true
@[expose] public section

/-! The finite excluded dyadic rows retain the actual exceptional
primitive zeros and the possible principal denominator. The principal
part contributes at most one row by the same sixth-class separation. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)
variable {ι : Type} [Fintype ι] (f : ι → {u : sourceRing F S₀ // u ≠ 0})
local notation "I" => SourceNonprincipalTwistRow F hζ S₀ η hM f
local notation "E" => sourceRowTwistDyadicExceptionalRows F S₀ hζ η hM f

def sourceRowTwistDyadicExcludedRows (U r : ℝ) : Finset ι :=
  (Finset.univ.filter (fun i => ¬ (sourceRowKummerTwist F hζ S₀
    (f i).val (f i).property η hM).IsNonprincipal)) ∪
    (E U r).map (⟨Subtype.val, Subtype.val_injective⟩ : I ↪ ι)

local notation "B" => sourceRowTwistDyadicExcludedRows F S₀ hζ η hM f

theorem sourceRowTwistDyadicExcludedRows_card_le (U r : ℝ)
    (hf : ∀ i j, (∃ a : F, a ^ 6 = ((f i).val : F) / ((f j).val : F)) → i = j) :
    (B U r).card ≤ 1+(E U r).card := by
  unfold sourceRowTwistDyadicExcludedRows
  apply (Finset.card_union_le _ _).trans
  rw [Finset.card_map]
  exact Nat.add_le_add_right (sourceRowPrincipalTwists_card_le_one F hζ S₀ η hM f hf) _

theorem sourceRowTwistDyadicExcludedRows_real_card_bound (U r C : ℝ) (hU : 1 ≤ U)
    (hf : ∀ i j, (∃ a : F, a ^ 6 = ((f i).val : F) / ((f j).val : F)) → i = j)
    (hE : ((E U r).card : ℝ) ≤ C*U^(1/2 : ℝ)) :
    ((B U r).card : ℝ) ≤ (1+C)*U^(1/2 : ℝ) := by
  have h : ((B U r).card : ℝ) ≤ 1+((E U r).card : ℝ) := by
    exact_mod_cast sourceRowTwistDyadicExcludedRows_card_le F S₀ hζ η hM f U r hf
  have hU' : 1 ≤ U^(1/2 : ℝ) := Real.one_le_rpow hU (by norm_num)
  calc
    _ ≤ _ := h
    _ ≤ U^(1/2 : ℝ)+C*U^(1/2 : ℝ) := add_le_add hU' hE
    _ = _ := by ring

theorem sourceRowTwistDyadicExcludedRows_not_mem_iff (U r : ℝ) (i : ι) :
    i ∉ B U r ↔ ∃ hi : (sourceRowKummerTwist F hζ S₀ (f i).val (f i).property η hM).IsNonprincipal,
      (⟨i, hi⟩ : I) ∉ E U r := by
  constructor
  · intro h
    have hi : (sourceRowKummerTwist F hζ S₀ (f i).val (f i).property η hM).IsNonprincipal := by
      by_contra hn
      exact h (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩))
    refine ⟨hi, ?_⟩
    intro he
    exact h (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨⟨i,hi⟩, he, rfl⟩))
  · rintro ⟨hi, he⟩ h
    rcases Finset.mem_union.mp h with h | h
    · exact (Finset.mem_filter.mp h).2 hi
    · obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp h
      have heq : j = (⟨i, hi⟩ : I) := Subtype.ext hji
      exact he (heq ▸ hj)

theorem sourceRowTwistDyadicExcludedRows_complement_reciprocalDomain
    (U r : ℝ) (hU : 0 ≤ U) (hr : 0 ≤ r) (i : ι) (hi : i ∉ B U r)
    (z : ℂ) (hz : (249/250 : ℝ) ≤ z.re) (him : |z.im| ≤ 4*U^r) :
    z ∈ sourceRayReciprocalDomain F (sourceRowKummerTwist F hζ S₀
      (f i).val (f i).property η hM)
      (sourceRowTwistFamilyOldModulus_ne_bot F S₀ hM f i) := by
  obtain ⟨hnp, hn⟩ := (sourceRowTwistDyadicExcludedRows_not_mem_iff F S₀ hζ η hM f U r i).mp hi
  exact sourceRowTwistDyadicExceptionalRows_complement_reciprocalDomain
    F S₀ hζ η hM f U r hU hr ⟨i,hnp⟩ hn z hz him

end
end ArtinMatthews.SourceEulerAssembly
