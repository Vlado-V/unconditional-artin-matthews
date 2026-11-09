module

public import ArtinMatthews.SourceAdditiveFractionSupport
public import ArtinMatthews.SourceProbeLogDilation
public import ArtinMatthews.SourceFrequencyOrbitSeparation


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField IsDedekindDomain AllowedGenerators Set
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "A" => SLocalAdditiveCompletionSpace F S
local notation "R" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "U" => SourceNonzeroFrequency F S₀

private def sourceAdditiveRatio (p : A × A) : A :=
  (fun w => p.1.1 w / p.2.1 w, fun v => p.1.2 v / p.2.2 v)

private def sourceCompactRatioBox (B : Set A) : Set A :=
  sourceAdditiveRatio F S₀ '' (B ×ˢ B)

private theorem sourceCompactRatioBox_isCompact (B : Set A) (hB : IsCompact B)
    (hzero : ∀ y ∈ B, (∀ w : InfinitePlace F, y.1 w ≠ 0) ∧ (∀ v : S, y.2 v ≠ 0)) :
    IsCompact (sourceCompactRatioBox F S₀ B) := by
  apply (hB.prod hB).image_of_continuousOn
  apply ContinuousOn.prodMk
  · apply continuousOn_pi.mpr
    intro w
    exact (((continuous_apply w).comp (continuous_fst.comp continuous_fst)).continuousOn).div
      (((continuous_apply w).comp (continuous_fst.comp continuous_snd)).continuousOn)
      (fun p hp => (hzero p.2 hp.2).1 w)
  · apply continuousOn_pi.mpr
    intro v
    exact (((continuous_apply v).comp (continuous_snd.comp continuous_fst)).continuousOn).div
      (((continuous_apply v).comp (continuous_snd.comp continuous_snd)).continuousOn)
      (fun p hp => (hzero p.2 hp.2).2 v)

private theorem sourcePositiveScaling_one : sLocalPositiveScaling F hζ S 1 = 1 := by
  let a := sLocalPositiveScaling F hζ S 1
  have h : a = a * a := by
    simpa only [one_mul] using sLocalPositiveScaling_mul F hζ S zero_lt_one zero_lt_one
  exact mul_left_cancel (h.symm.trans (mul_one a).symm)

/-- Ratios of two rows in the same exterior ideal are genuine source-ring units. -/
theorem sourceEqualExteriorRows_associated (m₀ m : U)
    (he : sourceElementExponents F S₀ m₀.val m₀.property =
      sourceElementExponents F S₀ m.val m.property) : Associated m₀.val m.val := by
  apply Ideal.span_singleton_eq_span_singleton.mp
  rw [← sourceElementExponents_ideal F S₀ m₀.val m₀.property,
    ← sourceElementExponents_ideal F S₀ m.val m.property, he]

private theorem sourceUnitRatio_mem_compact_rows (B : Set A)
    (hzero : ∀ y ∈ B, (∀ w : InfinitePlace F, y.1 w ≠ 0) ∧ (∀ v : S, y.2 v ≠ 0))
    (N : ℝ) (m₀ m : R) (hm₀ : m₀ ∈ sourceScaledLatticeRows F S₀ hζ B N)
    (hm : m ∈ sourceScaledLatticeRows F S₀ hζ B N) (u : Rˣ) (hu : m₀ * (u : R) = m) :
    (u : R) ∈ sourceScaledLatticeRows F S₀ hζ (sourceCompactRatioBox F S₀ B) 1 := by
  obtain ⟨x₀, hx₀, he₀⟩ := hm₀
  obtain ⟨x, hx, he⟩ := hm
  let a := sLocalPositiveScaling F hζ S N
  let b := sLocalRingDiagonal F S ((u : R) : F)
  have hprod : sLocalRingDiagonal F S (m₀ : F) * b = sLocalRingDiagonal F S (m : F) := by
    rw [← hu, Subalgebra.coe_mul, map_mul]
  have hmul : x₀ * b = x := by
    rw [← he₀, ← he] at hprod
    have hh := congrArg (fun y : A => sourceSLocalUnitAdditivePoint F S a⁻¹ * y) hprod
    change sourceSLocalUnitAdditivePoint F S a⁻¹ * ((sourceSLocalUnitAdditivePoint F S a * x₀) * b) =
      sourceSLocalUnitAdditivePoint F S a⁻¹ * (sourceSLocalUnitAdditivePoint F S a * x) at hh
    simpa only [← mul_assoc, ← sourceSLocalUnitAdditivePoint_mul, inv_mul_cancel,
      show sourceSLocalUnitAdditivePoint F S 1 = 1 from rfl, one_mul] using hh
  have hr : sourceAdditiveRatio F S₀ (x, x₀) = b := by
    apply Prod.ext
    · funext w
      change x.1 w / x₀.1 w = b.1 w
      apply (div_eq_iff ((hzero x₀ hx₀).1 w)).mpr
      rw [mul_comm]
      exact (congrArg (fun y : A => y.1 w) hmul).symm
    · funext v
      change x.2 v / x₀.2 v = b.2 v
      apply (div_eq_iff ((hzero x₀ hx₀).2 v)).mpr
      rw [mul_comm]
      exact (congrArg (fun y : A => y.2 v) hmul).symm
  refine ⟨sourceAdditiveRatio F S₀ (x, x₀), ⟨(x, x₀), ⟨hx, hx₀⟩, rfl⟩, ?_⟩
  change sourceSLocalUnitAdditivePoint F S (sLocalPositiveScaling F hζ S 1) *
    sourceAdditiveRatio F S₀ (x, x₀) = b
  rw [sourcePositiveScaling_one F S₀ hζ, show sourceSLocalUnitAdditivePoint F S 1 = 1 from rfl,
    one_mul, hr]

/-- A fixed compact quotient box contains the genuine ratios within each
exterior ideal fiber, so its discrete source lattice bounds every fiber. -/
theorem sourceScaledLatticeRows_exteriorFibers_card_le (B : Set A) (hB : IsCompact B)
    (hzero : ∀ y ∈ B, (∀ w : InfinitePlace F, y.1 w ≠ 0) ∧ (∀ v : S, y.2 v ≠ 0)) :
    ∃ K : ℕ, ∀ N : ℝ, ∀ M : Finset U,
      (∀ m ∈ M, m.val ∈ sourceScaledLatticeRows F S₀ hζ B N) → ∀ e : E,
      (M.filter (fun m => sourceElementExponents F S₀ m.val m.property = e)).card ≤ K := by
  have hfin := sourceScaledLatticeRows_finite F S₀ hζ (sourceCompactRatioBox F S₀ B)
    (sourceCompactRatioBox_isCompact F S₀ B hB hzero) (N := 1) zero_lt_one
  let Q := hfin.toFinset
  refine ⟨Q.card, fun N M hM e => ?_⟩
  let T := M.filter (fun m => sourceElementExponents F S₀ m.val m.property = e)
  change T.card ≤ Q.card
  by_cases hn : T.Nonempty
  · obtain ⟨m₀, hm₀⟩ := hn
    have hmem (m : T) : m.val.val ∈ sourceScaledLatticeRows F S₀ hζ B N :=
      hM m.val (Finset.mem_filter.mp m.property).1
    have hm₀' := hmem ⟨m₀, hm₀⟩
    have hAssoc (m : T) : Associated m₀.val m.val.val :=
      sourceEqualExteriorRows_associated F S₀ m₀ m.val
        ((Finset.mem_filter.mp hm₀).2.trans (Finset.mem_filter.mp m.property).2.symm)
    choose u hu using hAssoc
    let f (m : T) : Q := ⟨(u m : R), hfin.mem_toFinset.mpr
      (sourceUnitRatio_mem_compact_rows F S₀ hζ B hzero N m₀.val m.val.val hm₀' (hmem m) (u m) (hu m))⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have he : (u x : R) = (u y : R) := congrArg Subtype.val hxy
      apply Subtype.ext
      apply Subtype.ext
      exact (hu x).symm.trans ((congrArg (fun w : R => m₀.val * w) he).trans (hu y))
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty]
    exact Nat.zero_le _

end
end ArtinMatthews.SourcePhysical
