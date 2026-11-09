module

public import ArtinMatthews.CubicSievePrimeStatistic
public import ArtinMatthews.PositiveDensityCubicTraceMean


set_option backward.privateInPublic true
@[expose] public section

/-! The remaining cubic input on the actual candidate progression is
only the source coefficient estimate for finitely many supported numerators. -/

noncomputable section
namespace ArtinMatthews

open Filter Finset UpperHalfPlane OAI OAI.SevenEighths
open scoped BigOperators ContDiff Topology MatrixGroups

theorem cubicSieve_trace_has_supported_numerator {S : Finset ℤ} (hS : AdmissibleBases S)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ)
    (hχ : χ ∈ characterPairReps (H := Additive (integerCubicGaloisGroup S))) :
    ∃ (A : ℤ) (hA : A ≠ 0)
      (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein, y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein)),
      A ∣ (∏ a ∈ S, a) ^ 2 ∧
      ∀ (M : ℕ) (h₃ : 3 ∣ M) (U : Finset (ZMod M)ˣ),
        (∀ v ∈ U, ZMod.castHom h₃ (ZMod 3) (v : ZMod M) = 1) →
        ∀ (ε : ℝ) (Φ : ℝ → ℝ), (∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1) →
        ∀ T : ℝ, 1 < T → T < 2 → Function.support Φ ⊆ Set.Ioo 1 T →
        ∀ᶠ x : ℝ in atTop,
          giantCubicTracePrimeTest U S χ ε Φ T x =
            giantCubicCuspPrimeTest (actualCubicNumeratorHeckeThetaCuspForm A hA hnoncube)
              (fun p => giantUnitResidueIndicator U p) ε Φ T x := by
  classical
  obtain ⟨A, hA, hdiv, _, hnonprincipal, htrace⟩ :=
    cubicFourier_character_has_thetaTrace (fun a ha => (hS.2 a ha).1) χ
  have hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein, y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein) := by
    intro hy
    exact hnonprincipal (characterPairReps_nontrivial χ hχ)
      ((cubicNumeratorHeckeCharacter_principal_iff A hA).mpr hy)
  refine ⟨A, hA, hnoncube, hdiv, ?_⟩
  intro M h₃ U hU₃ ε Φ hΦ T hT₁ hT₂ hs
  let B := ∑ p ∈ giantCubicRamifiedPrimes S, p
  filter_upwards [giantSieveCandidates_structural_eventually hS U (fun _ => True) ε Φ hΦ hT₁ hT₂ hs,
    eventually_ge_atTop (B : ℝ)] with x hstruct hB
  unfold giantCubicTracePrimeTest giantCubicCuspPrimeTest
  apply sum_congr rfl
  intro p hp
  let w : ℂ := (giantSieveWeight Φ x p : ℂ) * giantUnitResidueIndicator U p *
    (((giantPrimeFactors (p - 1) x ε).card : ℝ) : ℂ)
  change w * giantCubicTraceAtPrime S χ p = w *
    (qExpansion 1 (actualCubicNumeratorHeckeThetaCuspForm A hA hnoncube)).coeff p
  by_cases hw : w = 0
  · simp only [hw, zero_mul]
  have hweight : giantSieveWeight Φ x p ≠ 0 := by
    intro hz
    exact hw (by simp [w, hz])
  have hgiant : (giantPrimeFactors (p - 1) x ε).Nonempty := by
    by_contra hnone
    exact hw (by simp [w, Finset.not_nonempty_iff_eq_empty.mp hnone])
  have hu : ∃ v ∈ U, (v : ZMod M) = p := by
    by_contra hnone
    have hi : giantUnitResidueIndicator U p = 0 := by
      unfold giantUnitResidueIndicator
      exact ite_eq_right (fun h => hnone (mem_image.mp h))
    exact hw (by simp [w, hi])
  have hmem : p ∈ giantSieveCandidates U (fun _ => True) ε Φ T x :=
    mem_giantSieveCandidates.mpr ⟨hp, hu, trivial, hweight, hgiant⟩
  have hp' := hstruct p hmem
  have hp₃ : p % 3 = 1 := by
    obtain ⟨v, hv, hvp⟩ := hu
    have hmod := hU₃ v hv
    rw [hvp, map_natCast] at hmod
    exact ((ZMod.natCast_eq_natCast_iff' p 1 3).mp
      (by simpa only [Nat.cast_one] using hmod)).trans (by decide)
  have hgood : p ∉ giantCubicRamifiedPrimes S := by
    intro hram
    have hpB : p ≤ B := single_le_sum (f := fun n : ℕ => n) (fun _ _ => Nat.zero_le _) hram
    exact (not_le_of_gt hp'.2.1.1) ((Nat.cast_le.mpr hpB).trans hB)
  let : Fact p.Prime := ⟨hp'.1⟩
  let D := Classical.choice (exists_integralFrobeniusData (integerCubicField S) hp'.1)
  have hnonzero (a : ℤ) (ha : a ∈ S) : ¬ (p : ℤ) ∣ a := fun h =>
    hp'.2.2.1 a ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr h)
  apply congrArg (w * ·)
  rw [actualCubicNumeratorHeckeThetaCuspForm_qExpansion_coeff]
  simpa only [giantCubicTraceAtPrime, dite_eq_left hp'.1, dite_eq_left hp₃, ite_eq_left hgood, D]
    using (htrace p hp₃ D hnonzero).symm

theorem cubicSieve_actual_trace_source_mean {S : Finset ℤ} (hS : AdmissibleBases S)
    {M : ℕ} [NeZero M] (h₃ : 3 ∣ M) (U : Finset (ZMod M)ˣ)
    (hU₃ : ∀ v ∈ U, ZMod.castHom h₃ (ZMod 3) (v : ZMod M) = 1)
    {ε T : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4) (hT₁ : 1 < T) (hT₂ : T < 2)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₀ : ∀ t, 0 ≤ Φ t) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 T)
    (hsource : ∀ (A : ℤ) (hA : A ≠ 0), A ∣ (∏ a ∈ S, a) ^ 2 →
      (¬ ∃ y : OAI.CubicFirstMoment.Eisenstein, y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein)) →
      ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
        GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x (ε / 1024) Cν)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ)
    (hχ : χ ∈ characterPairReps (H := Additive (integerCubicGaloisGroup S))) :
    Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) * giantCubicTracePrimeTest U S χ ε Φ T x)
      atTop (𝓝 0) := by
  obtain ⟨A, hA, hnoncube, hdiv, heq⟩ := cubicSieve_trace_has_supported_numerator hS χ hχ
  have hmean := cubicSieve_actual_cusp_source_progression_mean A hA hnoncube U hε hεq hT₁ hT₂
    Φ hΦ hΦ₀ hΦ₁ hs (hsource A hA hdiv hnoncube)
  apply hmean.congr'
  have hΦdata (t : ℝ) : 0 ≤ Φ t ∧ Φ t ≤ 1 :=
    ⟨hΦ₀ t, (by simpa only [Real.norm_eq_abs, abs_of_nonneg (hΦ₀ t)] using hΦ₁ t)⟩
  filter_upwards [heq M h₃ U hU₃ ε Φ hΦdata T hT₁ hT₂ hs] with x hx
  exact congrArg (((Real.log x / x : ℝ) : ℂ) * ·) hx.symm

end ArtinMatthews
