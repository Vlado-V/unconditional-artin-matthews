module

public import ArtinMatthews.SourceKPAdelicOutgoingSection


set_option backward.privateInPublic true
@[expose] public section

/-! Every actual outgoing coordinate is the corresponding left-torus
translate of the literal scalar trace integral, with its fixed half
modular scalar. This gives an exact interface for scalar continuation. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "G" => SourceKPAdelicProjective K hζ
local notation "T" => sourceKPAdelicCoveringTorus K hζ
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "O" => sourceKPAdelicOutgoingSection K hζ
local notation "I" => sourceKPAdelicTraceIntertwiner K hζ
local notation "d₀" => sourceKPAdelicBorelTorusInclusion K hζ
local notation "δ" => sourceKPAdelicBorelModularHalf K hζ

theorem sourceKPAdelicOutgoingSection_trace_coordinate (s : ℂ) (g : G) (t : T) :
    ((O s).val g).val t = (δ (d₀ t))⁻¹ * I s (t.val*g) := by
  have h := congrArg (fun v : V (-s) => v.val 1)
    ((O s).property (d₀ t) g)
  change ((O s).val (t.val*g)).val 1 =
    δ (d₀ t)*((O s).val g).val (1*sourceKPAdelicBorelTorusProjection K hζ (d₀ t)) at h
  rw [sourceKPAdelicBorelTorusProjection_inclusion,one_mul,
    sourceKPAdelicOutgoingSection_trace_one K hζ] at h
  have hn : δ (d₀ t) ≠ 0 := by
    change (sourceKPIdeleComplexNorm K (1/2 : ℂ)
      (sourceKPAdelicTorusIdele K hζ (sourceKPAdelicBorelTorusProjection K hζ (d₀ t))) : ℂ) ≠ 0
    exact Units.ne_zero _
  rw [h,← mul_assoc,inv_mul_cancel₀ hn,one_mul]

end
end ArtinMatthews
