module

public import ArtinMatthews.SourceKPDeepCubes
public import ArtinMatthews.SixthLocalHensel
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Cube roots for the actual matrix entries in a deep principal
congruence subgroup, at every finite place including the wild ones. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain IsLocalRing
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

def sourceKPDeepIdeal : Ideal (P.adicCompletionIntegers K) :=
  maximalIdeal (P.adicCompletionIntegers K) ^ sixthLocalHenselDepth P

theorem sourceKPDeepIdeal_le_maximal :
    sourceKPDeepIdeal K P ≤ maximalIdeal (P.adicCompletionIntegers K) :=
  Ideal.pow_le_self (Nat.ne_zero_of_lt (sixthLocalHenselDepth_pos P))

theorem sourceKPDeepEntry_isUnit (x : P.adicCompletionIntegers K)
    (hx : x-1 ∈ sourceKPDeepIdeal K P) : IsUnit x := by
  have hr : residue (P.adicCompletionIntegers K) (x-1) = 0 :=
    (residue_eq_zero_iff _).mpr (sourceKPDeepIdeal_le_maximal K P hx)
  have he : residue (P.adicCompletionIntegers K) x = 1 := by
    simpa only [map_sub, map_one, sub_eq_zero] using hr
  exact (residue_ne_zero_iff_isUnit x).mp (he ▸ one_ne_zero)

theorem sourceKPDeepEntry_cube (x : P.adicCompletionIntegers K)
    (hx : x-1 ∈ sourceKPDeepIdeal K P) :
    ∃ a : (P.adicCompletion K)ˣ,
      algebraMap (P.adicCompletionIntegers K) (P.adicCompletion K) x =
        ((a^3 : (P.adicCompletion K)ˣ) : P.adicCompletion K) := by
  let hu := sourceKPDeepEntry_isUnit K P x hx
  let u : (P.adicCompletionIntegers K)ˣ := hu.unit
  have huval : (u : P.adicCompletionIntegers K) = x := hu.unit_spec
  obtain ⟨w,hw⟩ := sixthLocal_exists_root P u (by rw [huval]; exact hx)
  let m : (P.adicCompletionIntegers K)ˣ →* (P.adicCompletion K)ˣ :=
    Units.map (algebraMap (P.adicCompletionIntegers K) (P.adicCompletion K)).toMonoidHom
  refine ⟨m (w^2), ?_⟩
  have he : (m (w^2))^3 = m u := by
    rw [← map_pow, ← pow_mul, show (2 : ℕ)*3=6 by decide, hw]
  rw [he]
  change algebraMap (P.adicCompletionIntegers K) (P.adicCompletion K) x =
    algebraMap (P.adicCompletionIntegers K) (P.adicCompletion K) (u : P.adicCompletionIntegers K)
  rw [huval]

end
end ArtinMatthews
