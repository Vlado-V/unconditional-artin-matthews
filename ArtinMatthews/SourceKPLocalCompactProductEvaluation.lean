module

public import ArtinMatthews.SourceKPLocalCompactProductLift


set_option backward.privateInPublic true
@[expose] public section

/-! At a fixed exterior remainder the actual global section descends
simultaneously through the right deep cosets at every retained place. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

abbrev SourceKPLocalCompactProductCosets :=
  (P : S) → (sourceKPLocalCompactCover K hζ P.val ⧸ sourceKPLocalCompactDeep K hζ P.val)

local notation "G" => SourceKPAdelicProjective K hζ
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "D" => sourceKPAdelicDeepCompact K hζ
local notation "F" => sourceKPAdelicCompactSection K hζ
local notation "ρ" => sourceKPAdelicNormalizedBorelRepresentation K hζ
local notation "Gₛ" => SourceKPLocalCompactProductGroup K hζ S
local notation "Bₛ" => SourceKPLocalCompactProductBorel K hζ S
local notation "Cₛ" => SourceKPLocalCompactProductCompact K hζ S
local notation "Jₛ" => SourceKPLocalCompactProductDeep K hζ S
local notation "Qₛ" => SourceKPLocalCompactProductCosets K hζ S
local notation "L" => sourceKPLocalCompactProductLift K hζ S
local notation "Lᴮ" => sourceKPLocalCompactProductBorelLift K hζ S

theorem sourceKPLocalCompactProductCosets_finite : Finite Qₛ := by
  letI (P : S) : Finite (sourceKPLocalCompactCover K hζ P.val ⧸
      sourceKPLocalCompactDeep K hζ P.val) := sourceKPLocalCompactCosets_finite K hζ P.val
  exact inferInstanceAs (Finite ((P : S) → (sourceKPLocalCompactCover K hζ P.val ⧸
    sourceKPLocalCompactDeep K hζ P.val)))

theorem sourceKPLocalCompactProductCosets_card :
    Nat.card Qₛ = ∏ P : S, Nat.card
      (sourceKPLocalCompactCover K hζ P.val ⧸ sourceKPLocalCompactDeep K hζ P.val) :=
  Nat.card_pi

theorem sourceKPLocalCompactProductSection_deep_right (s : ℂ) (r : G)
    (hr : ∀ P : S, sourceKPAdelicLocalBase K hζ P.val r = 1) (g : Gₛ) (j : Jₛ) :
    (F s).val (L (g*(fun P => (j P).val.val))*r) = (F s).val (L g*r) := by
  let j₀ : Gₛ := fun P => (j P).val.val
  let k : D := ⟨L j₀,sourceKPLocalCompactProductDeep_mem K hζ S j⟩
  have hc := sourceKPLocalCompactProductLift_commute_of_base_one K hζ S j₀ r hr
  change (F s).val (L (g*j₀)*r) = _
  rw [map_mul L,mul_assoc,hc.eq,← mul_assoc]
  exact congrArg (fun f : SourceKPAdelicPrincipalSeries K hζ s => f.val (L g*r))
    (sourceKPAdelicCompactSection_right K hζ s k)

def sourceKPLocalCompactProductEvaluation (s : ℂ) (r : G) (q : Qₛ) : V s :=
  (F s).val (L (fun P => (q P).out.val)*r)

theorem sourceKPLocalCompactProductEvaluation_apply (s : ℂ) (r : G)
    (hr : ∀ P : S, sourceKPAdelicLocalBase K hζ P.val r = 1) (k : Cₛ) :
    sourceKPLocalCompactProductEvaluation K hζ S s r (fun P => QuotientGroup.mk (k P)) =
      (F s).val (L (fun P => (k P).val)*r) := by
  let q : Qₛ := fun P => QuotientGroup.mk (k P)
  choose j hj using fun P : S =>
    QuotientGroup.mk_out_eq_mul (s := sourceKPLocalCompactDeep K hζ P.val) (k P)
  have he : (fun P : S => (q P).out.val) =
      (fun P : S => (k P).val) * (fun P : S => (j P).val.val) := by
    funext P
    exact congrArg Subtype.val (hj P)
  change (F s).val (L (fun P => (q P).out.val)*r) = _
  rw [he]
  exact sourceKPLocalCompactProductSection_deep_right K hζ S s r hr
    (fun P => (k P).val) j

theorem sourceKPLocalCompactProductSection_borel (s : ℂ) (r : G) (b : Bₛ) (g : Gₛ) :
    (F s).val (L ((fun P => (b P).val)*g)*r) = ρ s (Lᴮ b) ((F s).val (L g*r)) := by
  rw [map_mul L,mul_assoc,← sourceKPLocalCompactProductBorelLift_val K hζ S b]
  exact (F s).property (Lᴮ b) (L g*r)

end
end ArtinMatthews
