module

public import ArtinMatthews.SourceJacquetHaarDilation
public import ArtinMatthews.SourceJacquetShellVector


set_option backward.privateInPublic true
@[expose] public section

/-! The actual valuation balls split into an integral ball and finitely
many compact shells. Their dilation and finite Bochner decomposition
use the discrete valuation, including the zero point in the ball. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical Set
open scoped NumberField SourcePhysical Pointwise BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "B" => sourceLocalBall K P
local notation "ν₀" => sourceLocalValuation K P

def sourceJacquetValuationShell (l : ℤ) : Set L := B l \ B (l - 1)

theorem sourceJacquetValuationShell_mem (l : ℤ) (x : L) :
    x ∈ sourceJacquetValuationShell K P l ↔ ν₀ x = WithZero.exp l := by
  change ν₀ x ≤ WithZero.exp l ∧ ¬ν₀ x ≤ WithZero.exp (l - 1) ↔ ν₀ x = WithZero.exp l
  constructor
  · rintro ⟨hx, hn⟩
    have hl : WithZero.exp (l - 1) < ν₀ x := lt_of_not_ge hn
    have h0 : 0 < ν₀ x := (zero_le : 0 ≤ WithZero.exp (l - 1)).trans_lt hl
    have he := WithZero.exp_log h0.ne'
    rw [← he, WithZero.exp_le_exp] at hx
    rw [← he, WithZero.exp_lt_exp] at hl
    rw [← he, WithZero.exp_inj]
    omega
  · intro hx
    rw [hx, WithZero.exp_le_exp, WithZero.exp_le_exp]
    omega

theorem sourceJacquetValuationShell_isCompact (l : ℤ) : IsCompact (sourceJacquetValuationShell K P l) :=
  (sourceLocalBall_isCompact K P l).diff (sourceLocalBall_isOpen K P (l - 1))

theorem sourceJacquetValuationShell_mul_image (l j : ℤ) (t : Lˣ) (ht : ν₀ (t : L) = WithZero.exp j) :
    (fun x : L => (t : L) * x) '' sourceJacquetValuationShell K P l = sourceJacquetValuationShell K P (l + j) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [sourceJacquetValuationShell_mem, map_mul, ht, (sourceJacquetValuationShell_mem K P l u).mp hu,
      ← WithZero.exp_add, add_comm]
  · intro hx
    refine ⟨x / (t : L), ?_, ?_⟩
    · rw [sourceJacquetValuationShell_mem, map_div₀,
        (sourceJacquetValuationShell_mem K P (l + j) x).mp hx, ht, ← WithZero.exp_sub, add_sub_cancel_right]
    · field_simp [t.ne_zero]

theorem sourceJacquetBall_mul_image (l j : ℤ) (t : Lˣ) (ht : ν₀ (t : L) = WithZero.exp j) :
    (fun x : L => (t : L) * x) '' B l = B (l + j) := by
  change t • B l = _
  rw [sourceLocalBall_smul, ht, WithZero.log_exp]

theorem sourceJacquetDilation_norm (j : ℤ) (t : Lˣ) (ht : ν₀ (t : L) = WithZero.exp j) :
    (‖(t : L)‖ : ℂ) = sourceJacquetScale (Ideal.absNorm P.asIdeal : ℝ) (j : ℝ) := by
  rw [sourceLocalNorm_eq_zpow K P (t : L) t.ne_zero, ht, WithZero.log_exp, sourceJacquetScale, Real.rpow_intCast]

theorem sourceJacquetBall_succ (n : ℤ) :
    B (n + 1) = B n ∪ sourceJacquetValuationShell K P (n + 1) := by
  unfold sourceJacquetValuationShell
  rw [add_sub_cancel_right]
  have hsub : B n ⊆ B (n + 1) := by
    intro x hx
    exact (show ν₀ x ≤ WithZero.exp n from hx).trans (WithZero.exp_le_exp.mpr (by omega))
  ext x
  change x ∈ B (n + 1) ↔ x ∈ B n ∨ (x ∈ B (n + 1) ∧ x ∉ B n)
  constructor
  · intro hx
    by_cases h : x ∈ B n
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  · rintro (hx | hx)
    · exact hsub hx
    · exact hx.1

theorem sourceJacquetBall_integral_shells {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : L → V)
    (hzero : IntegrableOn f (B 0) (sourceJacquetHaar K P))
    (hshell : ∀ l : ℕ, 0 < l → IntegrableOn f (sourceJacquetValuationShell K P (l : ℤ)) (sourceJacquetHaar K P))
    (N : ℕ) :
    IntegrableOn f (B (N : ℤ)) (sourceJacquetHaar K P) ∧
      (∫ x in B (N : ℤ), f x ∂(sourceJacquetHaar K P)) =
        (∫ x in B 0, f x ∂(sourceJacquetHaar K P)) +
          ∑ l ∈ Finset.Icc 1 N, ∫ x in sourceJacquetValuationShell K P (l : ℤ), f x ∂(sourceJacquetHaar K P) := by
  induction N with
  | zero => exact ⟨hzero, by simp⟩
  | succ N ih =>
    have hs := hshell (N + 1) (Nat.succ_pos N)
    rw [Nat.cast_succ] at hs
    have hd : Disjoint (B (N : ℤ)) (sourceJacquetValuationShell K P ((N : ℤ) + 1)) := by
      rw [sourceJacquetValuationShell, add_sub_cancel_right]
      exact Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)
    rw [Nat.cast_succ, sourceJacquetBall_succ K P (N : ℤ)]
    refine ⟨ih.1.union hs, ?_⟩
    rw [setIntegral_union hd (sourceJacquetValuationShell_isCompact K P ((N : ℤ) + 1)).measurableSet ih.1 hs,
      ih.2, Finset.sum_Icc_succ_top (by omega), Nat.cast_succ, add_assoc]

end
end ArtinMatthews
