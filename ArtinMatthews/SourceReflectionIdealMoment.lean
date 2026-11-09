module

public import ArtinMatthews.SourceReflectionDyadicMoment


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ideal-row second moment for one fixed row-unit class,
with each row assigned to its two exact norm dyads. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {U : Type} [Fintype U] (A : SourceReflectionExpansionData F S₀ U)

local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "powerful" => sourceReflectionPowerfulPart
local notation "simple" => sourceReflectionSimplePart

def sourceReflectionIdealRow (Z : ℝ) (e : E) : ℂ :=
  sourceReflectionSelectedRow F S₀ hζ A Z (powerful e) (simple e) (fun _ => True)

theorem sourceReflectionIdealRows_fiberwise (X : Finset E) (w : E → E → ℝ) :
    (∑ e ∈ X, w (powerful e) (simple e)) =
      ∑ h ∈ X.image powerful, ∑ d ∈ (X.filter (fun e => powerful e = h)).image simple, w h d := by
  let H := X.image powerful
  have hf : (X : Set E).MapsTo powerful H := fun _ he => Finset.mem_image_of_mem _ he
  rw [← Finset.sum_fiberwise_of_maps_to hf (fun e => w (powerful e) (simple e))]
  apply Finset.sum_congr rfl
  intro h _
  let T := X.filter (fun e => powerful e = h)
  have hT (e : E) (he : e ∈ T) : powerful e = h := (Finset.mem_filter.mp he).2
  have hinj : Set.InjOn (fun e : E => simple e) (T : Set E) := by
    intro e he e' he' hd
    change simple e = simple e' at hd
    calc
      e = powerful e + simple e := (sourceReflectionPowerfulSimple_add e).symm
      _ = powerful e' + simple e' := by rw [hT e he, hT e' he', hd]
      _ = e' := sourceReflectionPowerfulSimple_add e'
  calc
    _ = ∑ e ∈ T, w h (simple e) :=
      Finset.sum_congr rfl (fun e he => congrArg (fun x => w x (simple e)) (hT e he))
    _ = _ := (Finset.sum_image hinj).symm

theorem exists_sourceReflectionIdealMoment_le
    (hsieve : SourceReflectionQuadraticSieve F S₀ hζ) {K M ε : ℝ}
    (hK : 1 ≤ K) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ X : Finset E,
      (∀ e ∈ X, (q e : ℝ) ≤ K * Z ^ M) →
      ∑ e ∈ X, ‖sourceReflectionIdealRow F S₀ hζ A Z e‖ ^ 2 ≤ C * Z ^ (2 * M - 1 + ε) := by
  obtain ⟨B, hB, hb⟩ := exists_sourceReflectionDyadicMoment_le F S₀ hζ A hsieve hK hM
    (show 0 < ε / 2 by positivity)
  obtain ⟨C, hC, hc⟩ := sourceReflectionSumDyadicBounds hK hM hε
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  intro Z hZ X hX
  let p (e : E) := q (powerful e)
  let d (e : E) := q (simple e)
  let w (e : E) := ‖sourceReflectionIdealRow F S₀ hζ A Z e‖ ^ 2
  have hnorm (e : E) : (p e : ℝ) * d e = q e := by
    exact_mod_cast sourceReflectionExteriorRow_norm F S₀ e
  apply hc Z hZ X p d w B hB.le
  · intro e he
    exact ⟨sourcePrimeExponentNorm_pos F S₀ _, sourcePrimeExponentNorm_pos F S₀ _,
      (hnorm e).le.trans (hX e he)⟩
  · intro j k
    let P := (2 : ℝ) ^ j
    let D := (2 : ℝ) ^ k
    let Y := X.filter (fun e => (Nat.log 2 (p e), Nat.log 2 (d e)) = (j,k))
    have hP : 1 ≤ P := one_le_pow₀ (by norm_num)
    have hD : 1 ≤ D := one_le_pow₀ (by norm_num)
    have hy (e : E) (he : e ∈ Y) :
        P ≤ (p e : ℝ) ∧ (p e : ℝ) < 2 * P ∧ D ≤ (d e : ℝ) ∧ (d e : ℝ) < 2 * D := by
      have he' := (Finset.mem_filter.mp he).2
      have hj := congrArg Prod.fst he'
      have hk := congrArg Prod.snd he'
      have hp' := sourceReflectionDyad_bounds (sourcePrimeExponentNorm_pos F S₀ (powerful e))
      have hd' := sourceReflectionDyad_bounds (sourcePrimeExponentNorm_pos F S₀ (simple e))
      change Nat.log 2 (q (powerful e)) = j at hj
      change Nat.log 2 (q (simple e)) = k at hk
      rw [hj] at hp'
      rw [hk] at hd'
      exact ⟨hp'.1, hp'.2, hd'.1, hd'.2⟩
    change (∑ e ∈ Y, w e) ≤ B * Z ^ (ε / 2) * Real.sqrt P * (D + D ^ 2 * P / Z)
    by_cases hY : Y.Nonempty
    · obtain ⟨e, he⟩ := hY
      have hPD : P * D ≤ K * Z ^ M :=
        (mul_le_mul (hy e he).1 (hy e he).2.2.1 (zero_le_one.trans hD) (Nat.cast_nonneg _)).trans
          ((hnorm e).le.trans (hX e (Finset.mem_filter.mp he).1))
      let H := Y.image powerful
      let R (h : E) := (Y.filter (fun e => powerful e = h)).image simple
      have hH (h : E) (hh : h ∈ H) : sourceReflectionIsPowerful h ∧ (q h : ℝ) ≤ 2 * P := by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hh
        exact ⟨sourceReflectionPowerfulPart_powerful x, (hy x hx).2.1.le⟩
      have hR (h : E) (r : E) (hr : r ∈ R h) :
          sourceReflectionIsSquarefree r ∧ D ≤ (q r : ℝ) ∧ (q r : ℝ) < 2 * D := by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
        exact ⟨sourceReflectionSimplePart_squarefree x, (hy x (Finset.mem_filter.mp hx).1).2.2⟩
      calc
        _ = ∑ h ∈ H, ∑ d ∈ R h, ‖sourceReflectionSelectedRow F S₀ hζ A Z h d (fun _ => True)‖ ^ 2 :=
          sourceReflectionIdealRows_fiberwise F S₀ Y _
        _ ≤ _ := hb Z P D hZ hP hD hPD H R hH (fun h _ r hr => hR h r hr)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hY, Finset.sum_empty]
      positivity

end
end ArtinMatthews.SourceEulerAssembly
