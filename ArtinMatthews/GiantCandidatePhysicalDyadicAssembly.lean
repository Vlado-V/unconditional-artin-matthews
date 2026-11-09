module

public import ArtinMatthews.GiantPhysicalDyadicLogSaving
public import ArtinMatthews.GiantRawDyadicGeometry
public import ArtinMatthews.GiantPhysicalRootLocalization


set_option backward.privateInPublic true
@[expose] public section

/-! The unmasked physical cutoff on the common box is estimated on the
enlarged moment slice of each relevant dyad. Both masks belong to this
estimate, leaving the original cutoff available for comparison stripping. -/
namespace ArtinMatthews
open Filter Finset
noncomputable section

universe u

theorem giantCandidatePhysicalCutoff_log_saving_of_local
    (k : ℕ) {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hτhi : τ ≤ 1/2)
    (Ψ : ℝ → ℂ) (hΨ : ∀ t < a, Ψ t = 0) (E : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ groups : Finset (GiantCandidateGroupIndex x),
      let P := fun j : ↥groups => giantCandidateGroup x j.val
      let Z := Ioc 0 ⌊x^2⌋₊
      ∀ (I : Type u) (patterns : Finset I) (C : I → ↥groups → Finset (Fin k))
        (ell : ℕ) (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
        (q ζ : ℝ) (f g : ℕ → ℂ),
        (∀ X : ℝ, x^τ ≤ X → X ≤ x^(1/τ) →
          ‖giantTwoSidedPhysicalCutoffPairing (Z := giantTwoSidedRootSlice X) patterns C 1 q ζ K Ψ x
            (fun r => if r ∈ Z then giantPhysicalDyadicLeft X f r else 0)
            (fun t => if t.val.1.val ∈ Z then g t.val.1.val else 0)‖ ≤ (Real.log x)^(-(E+2))) →
        ‖giantTwoSidedPhysicalCutoffPairing (Z := Z) patterns C 1 q ζ K Ψ x f
          (fun t => g t.val.1.val)‖ ≤ (Real.log x)^(-E) := by
  have hτ1 : τ < 1 := hτhi.trans_lt (by norm_num)
  filter_upwards [giantCandidatePhysicalCutoffPairing_eventually_eq_rootSlice.{u} k hτ,
    giantPhysicalDyadic_lowerCutoff_eventually ha hτ1, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1+3/Real.log 2),
    giantCandidateFullPrimes_prime_upper_eventually] with x hloc hsmall hx hL hprime
  intro groups P Z I patterns C ell K q ζ f g hlocal
  let N := ⌊x^2⌋₊
  have hN : (N : ℝ) ≤ x^2 := Nat.floor_le (sq_nonneg x)
  have hP (j : ↥groups) (p : ℕ) (hp : p ∈ P j) : p.Prime :=
    (hprime p (mem_giantCandidateFullPrimes.mpr ⟨j.val,hp⟩)).1
  have hx1 : 1 ≤ x := one_le_two.trans hx
  have hscale : x^2 ≤ x^(1/τ) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hx1 ((le_div_iff₀ hτ).2 (by linarith))
  apply giantTwoSidedPhysicalCutoffPairing_log_saving_of_dyads hP patterns C 1 q ζ K Ψ
    hx ha hsmall hL hΨ f (fun t => g t.val.1.val) N Subset.rfl hN E
  intro j hj hX
  let X : ℝ := ((2 ^ j : ℕ) : ℝ)
  have hXhi : X ≤ x^(1/τ) := (giantPhysicalDyadic_scale_le hx1 hN hj).trans hscale
  have hf : ∀ r ∉ giantTwoSidedRootInterval X, giantPhysicalDyadicLeft X f r = 0 := by
    intro r hr
    simp only [giantPhysicalDyadicLeft, if_neg hr]
  rw [hloc groups I patterns C ell K q ζ Ψ Z X hX (giantPhysicalDyadicLeft X f) g hf]
  exact hlocal X hX hXhi

end
end ArtinMatthews
