module

public import ArtinMatthews.FixedURootCount


set_option backward.privateInPublic true
@[expose] public section

/-! The counted congruence pairs are actual primitive first columns with
integral determinant-one completions and the prescribed completion residue. -/
namespace ArtinMatthews
open OAI.Erdos970 ErdosHyperbolaError

/-- Every counted pair has an actual determinant-one integer completion. -/
theorem fixedURootPairs_completion {u S : ℕ} {c₀ v₀ d₀ : ℤ}
    {x₀ x₁ y₀ y₁ : ℝ} {lcI rcI lcJ rcJ : Bool} {c v : ℤ}
    (hmem : (c,v) ∈ fixedURootPairs u S c₀ v₀ d₀ x₀ x₁ y₀ y₁ lcI rcI lcJ rcJ) :
    ∃ d : ℤ, (u : ℤ)*d-v*c = 1 ∧ Int.ModEq (S : ℤ) d d₀ := by
  have hp := (Finset.mem_filter.mp hmem).2.2.2
  exact (fixedURoot_completion_iff u S c v d₀).mp hp

/-- The determinant-one completion is unique for positive first coordinate. -/
theorem fixedURootPairs_completion_unique {u S : ℕ} (hu : 0 < u) {c₀ v₀ d₀ : ℤ}
    {x₀ x₁ y₀ y₁ : ℝ} {lcI rcI lcJ rcJ : Bool} {c v : ℤ}
    (hmem : (c,v) ∈ fixedURootPairs u S c₀ v₀ d₀ x₀ x₁ y₀ y₁ lcI rcI lcJ rcJ) :
    ∃! d : ℤ, (u : ℤ)*d-v*c = 1 ∧ Int.ModEq (S : ℤ) d d₀ := by
  obtain ⟨d,hd⟩ := fixedURootPairs_completion hmem
  refine ⟨d,hd,?_⟩
  intro e he
  apply mul_left_cancel₀ (show (u : ℤ) ≠ 0 by exact_mod_cast hu.ne')
  linarith [he.1,hd.1]

/-- The counted first column is primitive; this is a consequence of its
completion, rather than an extra filtering assumption. -/
theorem fixedURootPairs_first_column_coprime {u S : ℕ} {c₀ v₀ d₀ : ℤ}
    {x₀ x₁ y₀ y₁ : ℝ} {lcI rcI lcJ rcJ : Bool} {c v : ℤ}
    (hmem : (c,v) ∈ fixedURootPairs u S c₀ v₀ d₀ x₀ x₁ y₀ y₁ lcI rcI lcJ rcJ) :
    u.Coprime v.natAbs := by
  obtain ⟨d,hd,_⟩ := fixedURootPairs_completion hmem
  have hc : IsCoprime (u : ℤ) v := by
    refine ⟨d,-c,?_⟩
    linear_combination hd
  apply Nat.coprime_iff_gcd_eq_one.mpr
  simpa only [Int.gcd_def,Int.natAbs_natCast] using
    (Int.isCoprime_iff_gcd_eq_one.mp hc)

end ArtinMatthews
