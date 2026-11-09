module

public import ArtinMatthews.SourceKPJacquetTinyUnits
public import ArtinMatthews.SourceKPDeepHensel


set_option backward.privateInPublic true
@[expose] public section

/-! A literal sufficiently deep principal-unit ball consists of sixth
powers in each retained completion, including the primes above two and three. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain SourcePhysical
open scoped NumberField SourcePhysical

noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "O" => P.adicCompletionIntegers K
local notation "B" => sourceLocalBall K P

theorem sourceKPRetained_tiny_sixth :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ t : Lˣ, ((t:L)-1) ∈ B (-(M:ℤ)) → ∃ w : Lˣ, w^6 = t := by
  obtain ⟨M,hM,hdeep⟩ := sourceKPJacquet_deep_ball_subset K P
  refine ⟨M,hM,fun t ht => ?_⟩
  obtain ⟨r,hr,he⟩ := hdeep ht
  change r ∈ sourceKPDeepIdeal K P at hr
  let x : O := 1+r
  have hx : x-1 ∈ sourceKPDeepIdeal K P := by simpa only [x,add_sub_cancel_left] using hr
  let h := sourceKPDeepEntry_isUnit K P x hx
  let u : Oˣ := h.unit
  have hu : (u:O) = x := h.unit_spec
  obtain ⟨w,hw⟩ := sixthLocal_exists_root P u (by rw [hu]; exact hx)
  let f : Oˣ →* Lˣ := Units.map (algebraMap O L).toMonoidHom
  refine ⟨f w,?_⟩
  rw [← map_pow, hw]
  apply Units.ext
  change algebraMap O L (u:O) = (t:L)
  rw [hu]
  dsimp only [x]
  rw [map_add,map_one,he]
  ring

end
end ArtinMatthews
